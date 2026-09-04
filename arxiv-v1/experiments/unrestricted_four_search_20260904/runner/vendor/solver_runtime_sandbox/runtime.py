from __future__ import annotations

import hashlib
import json
import math
import os
import queue
import random
import re
import threading
import time
import uuid
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Protocol

from solver_runtime_sandbox.judge import JudgeV3Client
from solver_runtime_sandbox.models import (
    MAX_FALSE_CERT_BYTES,
    MAX_LEAN_CODE_BYTES,
    MAX_SOLVER_BYTES,
    JudgeAttempt,
    SandboxCreateErrorRecord,
    SandboxRunResult,
    Stage2Problem,
)
from solver_runtime_sandbox.settings import Settings

MAX_PROTOCOL_LINE_CHARS = 1 * 1024 * 1024
MAX_STDERR_TAIL_CHARS = 64 * 1024
MAX_PROTOCOL_LOG_ENTRIES = 100
SANDBOX_SUBMISSION_DIR = "/tmp/stage2-solver/submission"
SANDBOX_SOLVER_PATH = f"{SANDBOX_SUBMISSION_DIR}/solver.py"
SANDBOX_MEMORY_MONITOR_PATH = f"{SANDBOX_SUBMISSION_DIR}/memory_monitor.py"
SANDBOX_RUN_ROOT = "/tmp/stage2-solver-runs"


def _runtime_debug(message: str) -> None:
    path = os.environ.get("SOLVER_RUNTIME_DEBUG_FILE")
    if not path:
        return
    with Path(path).open("a", encoding="utf-8") as handle:
        handle.write(f"{time.monotonic():.6f} {message}\n")
        handle.flush()


class SandboxFactory(Protocol):
    def __call__(self, settings: Settings) -> Any: ...


class SandboxConnector(Protocol):
    def __call__(self, settings: Settings, sandbox_id: str) -> Any: ...


class JudgeClient(Protocol):
    def verify(
        self,
        *,
        problem: Stage2Problem,
        verdict: str,
        code: str,
        lean_timeout_seconds: int | None = None,
    ) -> dict[str, Any]: ...


class SandboxCreationFailed(RuntimeError):
    def __init__(
        self,
        last_error: Exception,
        *,
        create_attempts: int,
        create_errors: list[SandboxCreateErrorRecord],
        create_elapsed_seconds: float,
    ) -> None:
        self.create_attempts = create_attempts
        self.create_errors = create_errors
        self.create_elapsed_seconds = create_elapsed_seconds
        self.display_error = f"{type(last_error).__name__}: {last_error}"[:4000]
        super().__init__(self.display_error)


@dataclass
class _RunState:
    run_id: str
    sandbox_id: str | None
    problem: Stage2Problem
    started: float
    solver_started: float
    create_attempts: int
    create_errors: list[SandboxCreateErrorRecord]
    create_elapsed_seconds: float
    attempts: list[JudgeAttempt] = field(default_factory=list)
    judge_calls: int = 0
    judge_elapsed_seconds: float = 0.0
    judge_remote_elapsed_seconds: float = 0.0
    protocol_log: list[str] = field(default_factory=list)
    stderr_tail: str = ""
    llm_calls: int = 0
    solver_exit_code: int | None = None


class SolverSandboxSession:
    """One uploaded solver in one Sandbox, reused for sequential problems."""

    def __init__(
        self,
        runtime: SolverSandboxRuntime,
        sandbox: Any,
        *,
        create_attempts: int,
        create_errors: list[SandboxCreateErrorRecord],
        create_elapsed_seconds: float,
        kill_on_close: bool = True,
    ) -> None:
        self._runtime = runtime
        self._sandbox = sandbox
        self._create_attempts = create_attempts
        self._create_errors = create_errors
        self._create_elapsed_seconds = create_elapsed_seconds
        self._closed = False
        self._kill_on_close = kill_on_close
        # Do not assume the control plane honoured Sandbox.create(timeout=...).
        # Some otherwise healthy instances have retained the service default
        # lease and disappeared after roughly ten minutes during a 2400-second
        # solver run.  Force exactly one explicit renewal before first use;
        # subsequent reused problems still share the locally tracked lease.
        self._lease_deadline = 0.0

    def run(
        self,
        *,
        problem: Stage2Problem,
        timeout_seconds: int | None = None,
    ) -> SandboxRunResult:
        if self._closed:
            raise RuntimeError("Sandbox session is closed")
        active_timeout = min(
            max(1, timeout_seconds or self._runtime.settings.solver_timeout_seconds),
            self._runtime.settings.solver_timeout_seconds,
        )
        now = time.monotonic()
        # Leave one minute for protocol/Judge teardown.  Refresh only when the
        # current lease cannot cover the next problem; a 300-second batch can
        # therefore reuse a sandbox for many tasks without touching the
        # control plane, while 2400/3600-second sessions still renew as needed.
        maximum_judge_wait = (
            0
            if self._runtime._generation_only
            else self._runtime.settings.max_judge_calls * 330
        )
        if now + active_timeout + maximum_judge_wait + 60 > self._lease_deadline:
            try:
                lease_seconds = (
                    self._runtime.settings.solver_timeout_seconds
                    + maximum_judge_wait
                    + 120
                )
                self._runtime.renew_sandbox_timeout(self._sandbox, lease_seconds)
            except AttributeError:
                # Test doubles and older compatible clients may not expose TTL
                # renewal; their lifetime is managed by the caller.
                self._lease_deadline = float("inf")
            else:
                self._lease_deadline = (
                    now + lease_seconds
                )
        create_attempts = self._create_attempts
        create_errors = self._create_errors
        create_elapsed_seconds = self._create_elapsed_seconds
        self._create_attempts = 0
        self._create_errors = []
        self._create_elapsed_seconds = 0.0
        return self._runtime._run_on_sandbox(
            sandbox=self._sandbox,
            problem=problem,
            timeout_seconds=timeout_seconds,
            create_attempts=create_attempts,
            create_errors=create_errors,
            create_elapsed_seconds=create_elapsed_seconds,
        )

    def close(self) -> None:
        if self._closed:
            return
        self._closed = True
        if not self._kill_on_close:
            return
        _runtime_debug("session_close_start")
        _bounded_sandbox_kill(
            self._sandbox,
            min(10.0, self._runtime.settings.request_timeout_seconds),
        )
        _runtime_debug("session_close_end")

    @property
    def sandbox_id(self) -> str:
        return str(getattr(self._sandbox, "sandbox_id", ""))

    def discard(self) -> None:
        """Kill a retained session after a health or execution failure."""

        if self._closed:
            return
        self._closed = True
        _bounded_sandbox_kill(
            self._sandbox,
            min(10.0, self._runtime.settings.request_timeout_seconds),
        )

    def __enter__(self) -> SolverSandboxSession:
        return self

    def __exit__(self, *_exc: object) -> None:
        self.close()


class SolverSandboxRuntime:
    def __init__(
        self,
        settings: Settings,
        *,
        sandbox_factory: SandboxFactory | None = None,
        sandbox_connector: SandboxConnector | None = None,
        judge_client: JudgeClient | None = None,
        generation_only: bool = False,
        measure_memory: bool = False,
        memory_sample_interval: float = 0.25,
        memory_series_interval: float = 1.0,
        memory_first_window_seconds: float = 300.0,
        memory_limit_bytes: int | None = None,
        control_rate_per_second: int | None = None,
        judge_concurrency: int | None = None,
        judge_budget_seconds: float = 300.0,
        accepted_code_cache: Mapping[str, Mapping[str, str]] | None = None,
        sleep: Callable[[float], None] = time.sleep,
        random_uniform: Callable[[float, float], float] = random.uniform,
    ) -> None:
        self.settings = settings
        self._sandbox_factory = sandbox_factory or _create_e2b_sandbox
        self._sandbox_connector = sandbox_connector or _connect_e2b_sandbox
        self._creation_slots = threading.BoundedSemaphore(settings.create_rate)
        self._sleep = sleep
        self._random_uniform = random_uniform
        self._generation_only = generation_only
        self._measure_memory = measure_memory
        self._memory_sample_interval = memory_sample_interval
        self._memory_series_interval = memory_series_interval
        self._memory_first_window_seconds = memory_first_window_seconds
        self._memory_limit_bytes = memory_limit_bytes
        self._control_rate_interval = (
            1.0 / control_rate_per_second if control_rate_per_second is not None else None
        )
        self._control_rate_lock = threading.Lock()
        self._next_control_start = 0.0
        self._judge_slots = (
            threading.BoundedSemaphore(judge_concurrency)
            if judge_concurrency is not None
            else None
        )
        self._judge_budget_seconds = judge_budget_seconds
        self._accepted_code_cache: dict[str, dict[str, str]] = {}
        for problem_id, candidates in (accepted_code_cache or {}).items():
            if not isinstance(problem_id, str) or not problem_id:
                raise ValueError("accepted-code cache problem ids must be non-empty strings")
            validated: dict[str, str] = {}
            for code_sha256, cached_verdict in candidates.items():
                if (
                    not isinstance(code_sha256, str)
                    or len(code_sha256) != 64
                    or any(character not in "0123456789abcdef" for character in code_sha256)
                ):
                    raise ValueError("accepted-code cache keys must be lowercase SHA-256 hex")
                if cached_verdict not in {"true", "false"}:
                    raise ValueError("accepted-code cache verdicts must be true or false")
                validated[code_sha256] = cached_verdict
            if validated:
                self._accepted_code_cache[problem_id] = validated
        if memory_sample_interval <= 0 or memory_series_interval <= 0:
            raise ValueError("memory sampling intervals must be positive")
        if memory_first_window_seconds <= 0:
            raise ValueError("memory first-window duration must be positive")
        if memory_limit_bytes is not None and memory_limit_bytes <= 0:
            raise ValueError("memory limit must be positive")
        if control_rate_per_second is not None and control_rate_per_second <= 0:
            raise ValueError("control request rate must be positive")
        if judge_concurrency is not None and judge_concurrency <= 0:
            raise ValueError("judge concurrency must be positive")
        if judge_budget_seconds <= 0:
            raise ValueError("judge budget must be positive")
        if judge_client is not None:
            self._judge = judge_client
        elif settings.judge_v3_base_url:
            self._judge = JudgeV3Client(settings.judge_v3_base_url)
        else:
            self._judge = None

    def renew_sandbox_timeout(self, sandbox: Any, lease_seconds: int) -> None:
        """Renew one lease with paced starts and bounded transient retries."""

        for attempt in range(1, self.settings.create_max_attempts + 1):
            if self._control_rate_interval is not None:
                with self._control_rate_lock:
                    now = time.monotonic()
                    wait_seconds = max(0.0, self._next_control_start - now)
                    if wait_seconds:
                        self._sleep(wait_seconds)
                    self._next_control_start = (
                        max(self._next_control_start, time.monotonic())
                        + self._control_rate_interval
                    )
            try:
                sandbox.set_timeout(
                    lease_seconds,
                    request_timeout=self.settings.request_timeout_seconds,
                )
            except Exception as exc:  # noqa: BLE001
                retryable = _is_retryable_create_error(exc)
                if not retryable or attempt >= self.settings.create_max_attempts:
                    raise
                base = self.settings.create_backoff_seconds * (2 ** (attempt - 1))
                self._sleep(self._random_uniform(base, base * 1.5))
            else:
                return

    def run(
        self,
        *,
        solver_bytes: bytes,
        problem: Stage2Problem,
        timeout_seconds: int | None = None,
    ) -> SandboxRunResult:
        with self.open_session(solver_bytes=solver_bytes) as session:
            return session.run(
                problem=problem,
                timeout_seconds=timeout_seconds,
            )

    def open_session(
        self,
        *,
        solver_bytes: bytes,
        sandbox_id: str | None = None,
        retain_on_close: bool = False,
    ) -> SolverSandboxSession:
        """Create or reconnect one reusable Sandbox and upload the solver."""

        self.validate_solver(solver_bytes)
        if self._judge is None and not self._generation_only:
            raise RuntimeError("JUDGE_V3_BASE_URL is required before running a solver")
        if sandbox_id is None:
            sandbox, create_attempts, create_errors, create_elapsed_seconds = (
                self._create_sandbox_with_retry()
            )
        else:
            started = time.monotonic()
            sandbox = self._sandbox_connector(self.settings, sandbox_id)
            create_attempts, create_errors = 0, []
            create_elapsed_seconds = round(time.monotonic() - started, 3)
        try:
            sandbox.files.write(
                SANDBOX_SOLVER_PATH,
                solver_bytes,
                user=self.settings.sandbox_user,
                request_timeout=self.settings.request_timeout_seconds,
            )
            if self._measure_memory or self._memory_limit_bytes is not None:
                monitor_bytes = Path(__file__).with_name("memory_monitor.py").read_bytes()
                sandbox.files.write(
                    SANDBOX_MEMORY_MONITOR_PATH,
                    monitor_bytes,
                    user=self.settings.sandbox_user,
                    request_timeout=self.settings.request_timeout_seconds,
                )
        except BaseException:
            sandbox.kill()
            raise
        return SolverSandboxSession(
            self,
            sandbox,
            create_attempts=create_attempts,
            create_errors=create_errors,
            create_elapsed_seconds=create_elapsed_seconds,
            kill_on_close=not retain_on_close,
        )

    def _run_on_sandbox(
        self,
        *,
        sandbox: Any,
        problem: Stage2Problem,
        timeout_seconds: int | None,
        create_attempts: int,
        create_errors: list[SandboxCreateErrorRecord],
        create_elapsed_seconds: float,
    ) -> SandboxRunResult:
        active_timeout = min(
            max(1, timeout_seconds or self.settings.solver_timeout_seconds),
            self.settings.solver_timeout_seconds,
        )
        if self._judge is None and not self._generation_only:
            raise RuntimeError("JUDGE_V3_BASE_URL is required before running a solver")

        started = time.monotonic() - create_elapsed_seconds
        solver_started = time.monotonic()
        run_id = uuid.uuid4().hex
        run_dir = f"{SANDBOX_RUN_ROOT}/{run_id}"
        sandbox.files.make_dir(
            run_dir,
            user=self.settings.sandbox_user,
            request_timeout=self.settings.request_timeout_seconds,
        )
        state = _RunState(
            run_id=run_id,
            sandbox_id=str(getattr(sandbox, "sandbox_id", "")) or None,
            problem=problem,
            started=started,
            solver_started=solver_started,
            create_attempts=create_attempts,
            create_errors=create_errors,
            create_elapsed_seconds=create_elapsed_seconds,
        )
        _runtime_debug("run_state_ready")
        waiter: threading.Thread | None = None
        command: Any | None = None
        monitor_command: Any | None = None
        memory_metrics_path = f"{run_dir}/memory_metrics.json"
        try:
            event_queue: queue.Queue[tuple[str, Any]] = queue.Queue()
            command_text = f"python -B -u {SANDBOX_SOLVER_PATH}"
            relay_timeout = active_timeout
            maximum_judge_wait = (
                0 if self._generation_only else self.settings.max_judge_calls * 330
            )
            maximum_wall_timeout = active_timeout + maximum_judge_wait + 30
            command = sandbox.commands.run(
                command_text,
                background=True,
                stdin=True,
                user=self.settings.sandbox_user,
                cwd=run_dir,
                # The upstream SDK documents zero as unlimited, but the
                # Alibaba envd/ALB compatibility layer closes that stream at
                # its 1200-second default.  An explicit per-run bound keeps
                # 2400-second experiments alive while the relay below remains
                # the authoritative wall-clock limiter.
                timeout=maximum_wall_timeout,
                request_timeout=self.settings.request_timeout_seconds,
            )
            _runtime_debug("command_started")
            # Establish the envd command stream before the solver attempts its
            # first stdin read.  Without an attached wait stream, Alibaba envd
            # can expose an immediate EOF before send_stdin reaches the PID.
            waiter = _start_command_waiter(
                command,
                event_queue,
                sandbox=sandbox,
                stream_timeout_seconds=maximum_wall_timeout,
            )
            _runtime_debug("waiter_started")
            startup = {
                "problem": problem.model_dump(exclude_none=True),
                "budget": {
                    "timeout_seconds": active_timeout,
                    "max_code_length": MAX_LEAN_CODE_BYTES,
                    "max_false_cert_bytes": MAX_FALSE_CERT_BYTES,
                },
            }
            sandbox.commands.send_stdin(
                command.pid,
                json.dumps(startup, ensure_ascii=False) + "\n",
                request_timeout=self.settings.request_timeout_seconds,
            )
            _runtime_debug("startup_sent")
            # Alibaba envd can route interactive input only to the most
            # recently started command.  Deliver the protocol bootstrap before
            # starting the non-interactive memory sidecar.
            if self._measure_memory or self._memory_limit_bytes is not None:
                monitor_text = (
                    f"python -B -u {SANDBOX_MEMORY_MONITOR_PATH} "
                    f"--pid {command.pid} "
                    f"--metrics {memory_metrics_path} "
                    f"--timeout-seconds {maximum_wall_timeout} "
                    f"--first-window-seconds {self._memory_first_window_seconds} "
                    f"--sample-interval {min(self._memory_sample_interval, 0.05)} "
                    f"--series-interval {self._memory_series_interval}"
                )
                if self._memory_limit_bytes is not None:
                    monitor_text += f" --memory-limit-bytes {self._memory_limit_bytes}"
                monitor_command = sandbox.commands.run(
                    monitor_text,
                    background=True,
                    user=self.settings.sandbox_user,
                    cwd=run_dir,
                    timeout=maximum_wall_timeout,
                    request_timeout=self.settings.request_timeout_seconds,
                )
                _runtime_debug("memory_monitor_started")
            # Long-running standalone solvers emit a lightweight plain-text
            # heartbeat on this original stream.  Keeping the initial handle
            # avoids the Alibaba ALB bug where a fresh process-connect stream
            # can wait for its first event until a 504 even though the process
            # itself remains healthy.
            result = self._relay_protocol(
                sandbox=sandbox,
                command=command,
                event_queue=event_queue,
                state=state,
                timeout_seconds=relay_timeout,
            )
            if self._measure_memory or self._memory_limit_bytes is not None:
                memory_profile = self._read_memory_profile(
                    sandbox,
                    memory_metrics_path,
                )
                result = result.model_copy(update={"memory_profile": memory_profile})
            return result
        finally:
            _runtime_debug("command_finally_start")
            if waiter is not None:
                waiter.join(timeout=2.0)
                _runtime_debug("command_join1")
                if waiter.is_alive() and command is not None:

                    def kill_command() -> None:
                        try:
                            sandbox.commands.kill(
                                command.pid,
                                request_timeout=min(
                                    5.0,
                                    self.settings.request_timeout_seconds,
                                ),
                            )
                        except (AttributeError, TypeError):
                            command.kill()
                        except Exception:  # noqa: BLE001
                            pass

                    _call_bounded(kill_command, 5.0)
                    _runtime_debug("command_kill")
                    waiter.join(timeout=2.0)
            if monitor_command is not None:

                def kill_monitor() -> None:
                    try:
                        sandbox.commands.kill(
                            monitor_command.pid,
                            request_timeout=min(5.0, self.settings.request_timeout_seconds),
                        )
                    except (AttributeError, TypeError):
                        monitor_command.kill()
                    except Exception:  # noqa: BLE001
                        pass

                _call_bounded(kill_monitor, 5.0)
                _runtime_debug("memory_monitor_kill")
            _runtime_debug("command_finally_end")

    def _read_memory_profile(self, sandbox: Any, path: str) -> dict[str, Any]:
        last_error: Exception | None = None
        for _ in range(4):
            self._sleep(self._memory_sample_interval + 0.05)
            try:
                raw = sandbox.files.read(
                    path,
                    format="text",
                    user=self.settings.sandbox_user,
                    request_timeout=self.settings.request_timeout_seconds,
                )
                value = json.loads(raw)
                if isinstance(value, dict):
                    return value
                raise ValueError("memory profile is not a JSON object")
            except Exception as exc:  # noqa: BLE001
                last_error = exc
        return {
            "schema_version": 1,
            "monitor_error": f"{type(last_error).__name__}: {last_error}" if last_error else "unknown",
        }

    def _create_sandbox_with_retry(
        self,
    ) -> tuple[Any, int, list[SandboxCreateErrorRecord], float]:
        started = time.monotonic()
        errors: list[SandboxCreateErrorRecord] = []

        for attempt in range(1, self.settings.create_max_attempts + 1):
            try:
                # Hold a creation slot only while the request is in flight.
                # Backoff deliberately happens after leaving this context.
                with self._creation_slots:
                    sandbox = self._sandbox_factory(self.settings)
            except Exception as exc:  # noqa: BLE001
                retryable = _is_retryable_create_error(exc)
                will_retry = retryable and attempt < self.settings.create_max_attempts
                backoff_seconds = 0.0
                if will_retry:
                    base = self.settings.create_backoff_seconds * (2 ** (attempt - 1))
                    backoff_seconds = round(self._random_uniform(base, base * 1.5), 3)
                errors.append(
                    SandboxCreateErrorRecord(
                        attempt=attempt,
                        error_type=type(exc).__name__,
                        error=str(exc)[:4000],
                        retryable=retryable,
                        will_retry=will_retry,
                        backoff_seconds=backoff_seconds,
                    )
                )
                if not will_retry:
                    raise SandboxCreationFailed(
                        exc,
                        create_attempts=attempt,
                        create_errors=errors,
                        create_elapsed_seconds=round(time.monotonic() - started, 3),
                    ) from exc
                self._sleep(backoff_seconds)
            else:
                return (
                    sandbox,
                    attempt,
                    errors,
                    round(time.monotonic() - started, 3),
                )

        raise AssertionError("unreachable Sandbox creation retry state")

    def _relay_protocol(
        self,
        *,
        sandbox: Any,
        command: Any,
        event_queue: queue.Queue[tuple[str, Any]],
        state: _RunState,
        timeout_seconds: int,
    ) -> SandboxRunResult:
        stdout_buffer = ""
        deadline = state.solver_started + timeout_seconds
        command_done = False
        command_error: str | None = None

        while time.monotonic() < deadline:
            remaining = max(0.01, min(0.25, deadline - time.monotonic()))
            try:
                kind, payload = event_queue.get(timeout=remaining)
            except queue.Empty:
                continue

            if kind == "stderr":
                state.stderr_tail = (state.stderr_tail + _event_text(payload))[
                    -MAX_STDERR_TAIL_CHARS:
                ]
                continue
            if kind == "exit":
                command_done = True
                state.solver_exit_code = _exit_code(payload)
            elif kind == "wait_error":
                command_done = True
                command_error = str(payload)
            elif kind == "stdout":
                stdout_buffer += _event_text(payload)
                if len(stdout_buffer) > MAX_PROTOCOL_LINE_CHARS:
                    return self._result(
                        state,
                        status="protocol_error",
                        error="solver stdout protocol line exceeded 1 MiB",
                    )
                while "\n" in stdout_buffer:
                    line, stdout_buffer = stdout_buffer.split("\n", 1)
                    judge_elapsed_before = state.judge_elapsed_seconds
                    result = self._handle_line(
                        sandbox=sandbox,
                        command=command,
                        state=state,
                        line=line.rstrip("\r"),
                        judge_timeout_seconds=300,
                    )
                    deadline += state.judge_elapsed_seconds - judge_elapsed_before
                    if result is not None:
                        return result

            if command_done and event_queue.empty():
                if stdout_buffer.strip():
                    judge_elapsed_before = state.judge_elapsed_seconds
                    result = self._handle_line(
                        sandbox=sandbox,
                        command=command,
                        state=state,
                        line=stdout_buffer.rstrip("\r"),
                        judge_timeout_seconds=300,
                    )
                    deadline += state.judge_elapsed_seconds - judge_elapsed_before
                    if result is not None:
                        return result
                if command_error is not None:
                    # A process wait/connect stream failure is an envd/control-plane
                    # failure, not evidence that the solver process exited.  Treating
                    # it as solver_exit permanently poisons campaign results during a
                    # transient TLS or gateway outage.
                    return self._result(
                        state,
                        status="infrastructure_error",
                        error=f"sandbox command stream failed: {command_error}",
                    )
                return self._result(
                    state,
                    status="solver_exit",
                    error=(
                        "solver exited before judge acceptance "
                        f"(exit code {state.solver_exit_code})"
                    ),
                )

        _runtime_debug("relay_timeout")
        health_error = _sandbox_health_error(
            sandbox,
            request_timeout=self.settings.request_timeout_seconds,
        )
        if health_error is not None:
            # Do not call a problem unsolved when the timeout boundary coincides
            # with an unreachable Sandbox.  The campaign runner can reconnect or
            # replace the Sandbox and replay the same input.
            return self._result(
                state,
                status="infrastructure_error",
                error=(
                    "solver deadline reached while sandbox health could not be "
                    f"verified: {health_error}"
                ),
            )
        return self._result(
            state,
            status="solver_timeout",
            error=f"solver exceeded the {timeout_seconds}-second wall-clock limit",
        )

    def _handle_line(
        self,
        *,
        sandbox: Any,
        command: Any,
        state: _RunState,
        line: str,
        judge_timeout_seconds: int,
    ) -> SandboxRunResult | None:
        if not line.strip():
            return None
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            self._append_protocol_log(state, line)
            return None
        if not isinstance(message, dict):
            self._append_protocol_log(state, line)
            return None

        call = message.get("call")
        if call == "llm":
            state.llm_calls += 1
            self._send_response(
                sandbox,
                command,
                {"error": "LLM proxy is not configured in this runner"},
            )
            return None
        if call != "judge":
            self._send_response(
                sandbox,
                command,
                {"error": f"unsupported solver call: {call!r}"},
            )
            return None

        if len(state.attempts) >= self.settings.max_judge_calls:
            return self._result(
                state,
                status="rejected",
                error=f"solver exceeded the {self.settings.max_judge_calls}-call judge limit",
            )
        verdict = message.get("verdict")
        code = message.get("code")
        judge_failed = False
        if verdict not in {"true", "false"} or not isinstance(code, str) or not code:
            response = {"status": "malformed", "message": "invalid judge request"}
        elif len(code.encode("utf-8")) > MAX_LEAN_CODE_BYTES:
            response = {"status": "malformed", "message": "Lean code exceeds 100,000 bytes"}
        elif verdict == "false" and len(code.encode("utf-8")) > MAX_FALSE_CERT_BYTES:
            response = {
                "status": "malformed",
                "message": "false certificate exceeds 20,000 bytes",
            }
        else:
            if self._generation_only:
                response = {
                    "status": "generated",
                    "message": "proof captured without Judge verification",
                }
            else:
                code_sha256 = hashlib.sha256(code.encode("utf-8")).hexdigest()
                cached_verdict = self._accepted_code_cache.get(state.problem.id, {}).get(
                    code_sha256
                )
                if cached_verdict == verdict:
                    response = {
                        "status": "accepted",
                        "error_code": "ACCEPTED",
                        "message": "certificate accepted via trusted exact-code cache",
                        "verdict": verdict,
                        "cached": True,
                        "cache_kind": "trusted_exact_code_sha256",
                        "code_sha256": code_sha256,
                    }
                else:
                    remaining_judge_budget = min(
                        float(judge_timeout_seconds),
                        self._judge_budget_seconds - state.judge_remote_elapsed_seconds,
                    )
                    if remaining_judge_budget <= 0:
                        return self._result(
                            state,
                            status="rejected",
                            error=(
                                "solver exhausted the cumulative "
                                f"{self._judge_budget_seconds:g}-second judge budget"
                            ),
                        )
                    state.judge_calls += 1
                    judge_started = time.monotonic()
                    remote_started: float | None = None
                    try:
                        if self._judge_slots is None:
                            remote_started = time.monotonic()
                            response = self._judge.verify(
                                problem=state.problem,
                                verdict=verdict,
                                code=code,
                                lean_timeout_seconds=max(
                                    1,
                                    min(300, math.ceil(remaining_judge_budget)),
                                ),
                            )
                        else:
                            with self._judge_slots:
                                remote_started = time.monotonic()
                                response = self._judge.verify(
                                    problem=state.problem,
                                    verdict=verdict,
                                    code=code,
                                    lean_timeout_seconds=max(
                                        1,
                                        min(300, math.ceil(remaining_judge_budget)),
                                    ),
                                )
                    except Exception as exc:  # noqa: BLE001
                        response = {
                            "error": f"judge-v3 request failed: {type(exc).__name__}: {exc}"
                        }
                        judge_failed = True
                    finally:
                        judge_finished = time.monotonic()
                        state.judge_elapsed_seconds += judge_finished - judge_started
                        if remote_started is not None:
                            state.judge_remote_elapsed_seconds += (
                                judge_finished - remote_started
                            )

        state.attempts.append(
            JudgeAttempt(
                verdict=verdict if isinstance(verdict, str) else None,
                code=code if isinstance(code, str) else "",
                response=response,
                metadata=(
                    message.get("metadata")
                    if isinstance(message.get("metadata"), dict)
                    else None
                ),
            )
        )
        if not self._generation_only and judge_failed:
            return self._result(
                state,
                status="infrastructure_error",
                error=str(response["error"]),
            )
        if response.get("status") == "generated":
            return self._result(state, status="generated")
        self._send_response(sandbox, command, _solver_judge_response(response))
        if response.get("status") == "accepted":
            return self._result(state, status="accepted")
        if state.judge_remote_elapsed_seconds >= self._judge_budget_seconds:
            return self._result(
                state,
                status="rejected",
                error=(
                    "solver exhausted the cumulative "
                    f"{self._judge_budget_seconds:g}-second judge budget"
                ),
            )
        return None

    def _send_response(self, sandbox: Any, command: Any, response: dict[str, Any]) -> None:
        sandbox.commands.send_stdin(
            command.pid,
            json.dumps(response, ensure_ascii=False) + "\n",
            request_timeout=self.settings.request_timeout_seconds,
        )

    @staticmethod
    def validate_solver(solver_bytes: bytes) -> None:
        if not solver_bytes:
            raise ValueError("solver.py is empty")
        if len(solver_bytes) > MAX_SOLVER_BYTES:
            raise ValueError(
                f"solver.py is {len(solver_bytes)} bytes; official limit is {MAX_SOLVER_BYTES}"
            )
        try:
            solver_bytes.decode("utf-8")
        except UnicodeDecodeError as exc:
            raise ValueError("solver.py must be UTF-8 text") from exc

    @staticmethod
    def _append_protocol_log(state: _RunState, line: str) -> None:
        if len(state.protocol_log) < MAX_PROTOCOL_LOG_ENTRIES:
            state.protocol_log.append(line[:2000])

    @staticmethod
    def _result(
        state: _RunState,
        *,
        status: str,
        error: str | None = None,
    ) -> SandboxRunResult:
        last = state.attempts[-1] if state.attempts else None
        return SandboxRunResult(
            run_id=state.run_id,
            sandbox_id=state.sandbox_id,
            problem_id=state.problem.id,
            status=status,
            solved=status == "accepted",
            verdict=last.verdict if last and last.verdict in {"true", "false"} else None,
            code=last.code if last else None,
            judge_calls=state.judge_calls,
            llm_calls=state.llm_calls,
            create_attempts=state.create_attempts,
            create_errors=state.create_errors,
            create_elapsed_seconds=state.create_elapsed_seconds,
            attempts=state.attempts,
            elapsed_seconds=round(time.monotonic() - state.started, 3),
            solver_elapsed_seconds=round(
                max(
                    0.0,
                    time.monotonic()
                    - state.solver_started
                    - state.judge_elapsed_seconds,
                ),
                3,
            ),
            judge_elapsed_seconds=round(state.judge_elapsed_seconds, 3),
            judge_remote_elapsed_seconds=round(
                state.judge_remote_elapsed_seconds, 3
            ),
            solver_exit_code=state.solver_exit_code,
            protocol_log=state.protocol_log,
            stderr_tail=state.stderr_tail,
            error=error,
        )


_RETRYABLE_CREATE_STATUS = re.compile(r"(?<!\d)(?:429|502|503|504)(?!\d)")
_NON_RETRYABLE_CREATE_STATUS = re.compile(r"(?<!\d)(?:400|401|403|404|405|409|422)(?!\d)")
_NON_RETRYABLE_TLS_MARKERS = (
    "invalid peer certificate",
    "certificate verify failed",
    "unknownissuer",
    "ekuerror",
    "self signed certificate",
    "hostname mismatch",
)
_RETRYABLE_NETWORK_MARKERS = (
    "timed out",
    "timeout",
    "temporary failure",
    "eof occurred in violation of protocol",
    "unexpected eof",
    "connection reset",
    "connection aborted",
    "connection refused",
    "server disconnected",
    "network is unreachable",
    "name or service not known",
)


def _is_retryable_create_error(error: Exception) -> bool:
    chain: list[BaseException] = []
    current: BaseException | None = error
    while current is not None and current not in chain and len(chain) < 8:
        chain.append(current)
        current = current.__cause__ or current.__context__

    text = " ".join(f"{type(item).__name__}: {item}" for item in chain).lower()
    if any(marker in text for marker in _NON_RETRYABLE_TLS_MARKERS):
        return False
    if _NON_RETRYABLE_CREATE_STATUS.search(text):
        return False
    if _RETRYABLE_CREATE_STATUS.search(text):
        return True
    if any(isinstance(item, (TimeoutError, ConnectionError)) for item in chain):
        return True
    retryable_type_names = {
        "connecterror",
        "connecttimeout",
        "networkerror",
        "pooltimeout",
        "readtimeout",
        "remoteprotocolerror",
        "writetimeout",
    }
    if any(type(item).__name__.lower() in retryable_type_names for item in chain):
        return True
    return any(marker in text for marker in _RETRYABLE_NETWORK_MARKERS)


def _sandbox_health_error(sandbox: Any, *, request_timeout: float) -> str | None:
    """Return an infrastructure error when a timeout cannot be verified safely."""
    try:
        sandbox.commands.list(request_timeout=min(10.0, request_timeout))
    except (AttributeError, TypeError):
        # Compatible test doubles and older clients may not expose process
        # listing.  Preserve the historical timeout behavior for those clients.
        return None
    except Exception as exc:  # noqa: BLE001
        return f"{type(exc).__name__}: {exc}"[:4000]
    return None


def _create_e2b_sandbox(settings: Settings) -> Any:
    if not settings.e2b_api_key:
        raise RuntimeError("E2B_API_KEY is required")
    from e2b import Sandbox

    _configure_e2b_envd_trust(settings.sandbox_ca_cert)

    return Sandbox.create(
        template=settings.sandbox_template,
        api_key=settings.e2b_api_key,
        domain=settings.e2b_domain,
        timeout=(
            settings.solver_timeout_seconds
            + settings.max_judge_calls * 330
            + 120
        ),
        request_timeout=settings.request_timeout_seconds,
        allow_internet_access=False,
        # Alibaba/OpenKruise deployments can issue legacy non-e2b_ keys.
        validate_api_key=False,
    )


def _connect_e2b_sandbox(settings: Settings, sandbox_id: str) -> Any:
    if not settings.e2b_api_key:
        raise RuntimeError("E2B_API_KEY is required")
    from e2b import Sandbox

    _configure_e2b_envd_trust(settings.sandbox_ca_cert)
    return Sandbox.connect(
        sandbox_id,
        timeout=(
            settings.solver_timeout_seconds
            + settings.max_judge_calls * 330
            + 120
        ),
        api_key=settings.e2b_api_key,
        domain=settings.e2b_domain,
        request_timeout=settings.request_timeout_seconds,
        validate_api_key=False,
    )


def _configure_e2b_envd_trust(custom_ca: Path | None) -> None:
    """Configure the E2B 2.x sync envd transport with the private Sandbox CA.

    E2B's REST client honors ``SSL_CERT_FILE``, while its pyqwest-based envd
    RPC transport has a separate trust store. Register one shared transport
    before the first Sandbox RPC so files and commands trust the same CA.
    """
    if custom_ca is None:
        return
    if not custom_ca.is_file():
        raise FileNotFoundError(f"Sandbox CA certificate not found: {custom_ca}")

    from e2b.api import connection_retries
    from e2b.envd import client_sync
    from e2b.envd.client_shared import pool_idle_timeout, pool_max_idle_per_host
    from pyqwest import SyncHTTPTransport

    with client_sync._transport_lock:
        if None in client_sync._transports:
            return
        client_sync._transports[None] = client_sync.PlainHTTPErrorTransport(
            client_sync.ConnectionRetryTransport(
                SyncHTTPTransport(
                    tls_ca_cert=custom_ca.read_bytes(),
                    # SSL_CERT_FILE already points at a combined public/custom
                    # bundle. Loading that as a system store as well as passing
                    # the custom CA makes rustls reject this private chain with
                    # EkuError, so keep this envd-only pool on the explicit CA.
                    tls_include_system_certs=False,
                    proxy=None,
                    pool_idle_timeout=pool_idle_timeout,
                    pool_max_idle_per_host=pool_max_idle_per_host,
                ),
                max_retries=connection_retries,
            )
        )


def _start_command_waiter(
    command: Any,
    event_queue: queue.Queue[tuple[str, Any]],
    *,
    sandbox: Any | None = None,
    stream_timeout_seconds: int = 180,
) -> threading.Thread:
    def _wait() -> None:
        handle = command
        for reconnect in range(4):
            try:
                result = handle.wait(
                    on_stdout=lambda data: event_queue.put(("stdout", data)),
                    on_stderr=lambda data: event_queue.put(("stderr", data)),
                )
                event_queue.put(("exit", result))
                return
            except Exception as exc:  # noqa: BLE001
                if sandbox is None or reconnect >= 3:
                    event_queue.put(("wait_error", f"{type(exc).__name__}: {exc}"))
                    return
                try:
                    handle = sandbox.commands.connect(
                        command.pid,
                        timeout=stream_timeout_seconds,
                    )
                except Exception as reconnect_exc:  # noqa: BLE001
                    if reconnect >= 2:
                        event_queue.put(
                            (
                                "wait_error",
                                f"{type(reconnect_exc).__name__}: {reconnect_exc}",
                            )
                        )
                        return

    waiter = threading.Thread(target=_wait, name="e2b-command-wait", daemon=True)
    waiter.start()
    return waiter


def _bounded_sandbox_kill(sandbox: Any, request_timeout: float) -> None:
    """Best-effort bounded teardown; old/fake SDKs accept no kwargs."""

    def kill() -> None:
        try:
            sandbox.kill(request_timeout=request_timeout)
        except TypeError:
            sandbox.kill()
        except Exception:  # noqa: BLE001
            pass

    _call_bounded(kill, request_timeout)


def _call_bounded(callback: Callable[[], None], timeout: float) -> None:
    """Bound SDK calls even when a custom transport ignores its timeout."""

    worker = threading.Thread(
        target=callback,
        name="sandbox-bounded-cleanup",
        daemon=True,
    )
    worker.start()
    worker.join(timeout=max(0.05, timeout))


def _event_text(value: Any) -> str:
    if isinstance(value, str):
        return value
    data = getattr(value, "data", None)
    if isinstance(data, str):
        return data
    return str(value)


def _exit_code(result: Any) -> int | None:
    value = getattr(result, "exit_code", None)
    if value is None and isinstance(result, dict):
        value = result.get("exit_code")
    try:
        return int(value) if value is not None else None
    except (TypeError, ValueError):
        return None


def _solver_judge_response(response: dict[str, Any]) -> dict[str, Any]:
    allowed = {
        "status",
        "stderr",
        "stdout",
        "message",
        "error",
        "error_code",
        "cached",
        "control_cached",
        "proof_policy_rev",
    }
    return {key: value for key, value in response.items() if key in allowed}
