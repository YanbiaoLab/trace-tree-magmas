from __future__ import annotations

import json
import queue
import threading
import time
import uuid
from collections.abc import Callable, Iterable, Iterator
from concurrent.futures import FIRST_COMPLETED, Future, ThreadPoolExecutor, wait
from dataclasses import dataclass
from typing import Protocol

from pydantic import ValidationError

from solver_runtime_sandbox.models import SandboxRunResult, Stage2Problem


@dataclass(frozen=True)
class ProblemItem:
    input_line: int
    problem: Stage2Problem


@dataclass(frozen=True)
class BatchRunRecord:
    input_line: int
    result: SandboxRunResult

    def as_dict(self) -> dict[str, object]:
        return {"input_line": self.input_line, **self.result.model_dump(mode="json")}


class Runtime(Protocol):
    def run(
        self,
        *,
        solver_bytes: bytes,
        problem: Stage2Problem,
        timeout_seconds: int | None = None,
    ) -> SandboxRunResult: ...


class RuntimeSession(Protocol):
    @property
    def sandbox_id(self) -> str: ...

    def run(
        self,
        *,
        problem: Stage2Problem,
        timeout_seconds: int | None = None,
    ) -> SandboxRunResult: ...

    def close(self) -> None: ...

    def discard(self) -> None: ...


class SessionRuntime(Runtime, Protocol):
    def open_session(self, *, solver_bytes: bytes) -> RuntimeSession: ...


def _close_session_quietly(session: RuntimeSession) -> None:
    """Best-effort cleanup must never erase a per-problem run result."""

    try:
        session.close()
    except BaseException as exc:  # noqa: BLE001
        if isinstance(exc, (KeyboardInterrupt, SystemExit)):
            raise
        pass


class SolverSandboxBatchRunner:
    """Run a streaming problem source with a bounded, continuously refilled window."""

    def __init__(
        self,
        runtime: Runtime,
        *,
        solver_bytes: bytes,
        concurrency: int,
        timeout_seconds: int | None = None,
    ) -> None:
        if concurrency < 1:
            raise ValueError("concurrency must be at least 1")
        self.runtime = runtime
        self.solver_bytes = solver_bytes
        self.concurrency = concurrency
        self.timeout_seconds = timeout_seconds

    def run(self, problems: Iterable[ProblemItem]) -> Iterator[BatchRunRecord]:
        source = iter(problems)
        with ThreadPoolExecutor(
            max_workers=self.concurrency,
            thread_name_prefix="solver-sandbox-run",
        ) as executor:
            pending: dict[Future[SandboxRunResult], tuple[ProblemItem, float]] = {}
            source_exhausted = False

            while len(pending) < self.concurrency and not source_exhausted:
                source_exhausted = not self._submit_next(executor, source, pending)

            while pending:
                completed, _ = wait(pending, return_when=FIRST_COMPLETED)
                for future in completed:
                    item, started = pending.pop(future)
                    yield BatchRunRecord(
                        input_line=item.input_line,
                        result=self._future_result(future, item, started),
                    )
                    if not source_exhausted:
                        source_exhausted = not self._submit_next(executor, source, pending)

    def _submit_next(
        self,
        executor: ThreadPoolExecutor,
        source: Iterator[ProblemItem],
        pending: dict[Future[SandboxRunResult], tuple[ProblemItem, float]],
    ) -> bool:
        try:
            item = next(source)
        except StopIteration:
            return False
        started = time.monotonic()
        future = executor.submit(
            self.runtime.run,
            solver_bytes=self.solver_bytes,
            problem=item.problem,
            timeout_seconds=self.timeout_seconds,
        )
        pending[future] = (item, started)
        return True

    @staticmethod
    def _future_result(
        future: Future[SandboxRunResult],
        item: ProblemItem,
        started: float,
    ) -> SandboxRunResult:
        try:
            return future.result()
        except Exception as exc:  # noqa: BLE001
            return _exception_result(exc, item, started)


class PooledSolverSandboxBatchRunner:
    """Reuse each uploaded Sandbox for a sequence of independent problems."""

    def __init__(
        self,
        runtime: SessionRuntime,
        *,
        solver_bytes: bytes,
        concurrency: int,
        timeout_seconds: int | None = None,
        hold_sandboxes_until_round_end: bool = False,
        sandbox_ids: list[str] | None = None,
        retain_sandboxes: bool = False,
        pool_changed: Callable[[list[str]], None] | None = None,
    ) -> None:
        if concurrency < 1:
            raise ValueError("concurrency must be at least 1")
        self.runtime = runtime
        self.solver_bytes = solver_bytes
        self.concurrency = concurrency
        self.timeout_seconds = timeout_seconds
        self.hold_sandboxes_until_round_end = hold_sandboxes_until_round_end
        self.initial_sandbox_ids = list(dict.fromkeys(sandbox_ids or []))
        self.retain_sandboxes = retain_sandboxes
        self.pool_changed = pool_changed
        self._pool_lock = threading.Lock()
        self._sandbox_ids = set(self.initial_sandbox_ids)

    @property
    def sandbox_ids(self) -> list[str]:
        with self._pool_lock:
            return sorted(self._sandbox_ids)

    def _pool_replace(self, old: str | None, new: str | None) -> None:
        with self._pool_lock:
            if old:
                self._sandbox_ids.discard(old)
            if new:
                self._sandbox_ids.add(new)
            snapshot = sorted(self._sandbox_ids)
        if self.pool_changed is not None:
            self.pool_changed(snapshot)

    def run(self, problems: Iterable[ProblemItem]) -> Iterator[BatchRunRecord]:
        work: queue.Queue[ProblemItem] = queue.Queue()
        items = list(problems)
        for item in items:
            work.put(item)
        if not items:
            return

        completed: queue.Queue[BatchRunRecord] = queue.Queue()
        worker_count = min(self.concurrency, len(items))
        start_barrier = threading.Barrier(worker_count)
        release_barrier = (
            threading.Barrier(worker_count) if self.hold_sandboxes_until_round_end else None
        )

        def worker(worker_index: int) -> None:
            session: RuntimeSession | None = None
            assigned_id = (
                self.initial_sandbox_ids[worker_index]
                if worker_index < len(self.initial_sandbox_ids)
                else None
            )

            def open_worker_session(sandbox_id: str | None) -> RuntimeSession:
                if sandbox_id is None and not self.retain_sandboxes:
                    return self.runtime.open_session(solver_bytes=self.solver_bytes)
                return self.runtime.open_session(
                    solver_bytes=self.solver_bytes,
                    sandbox_id=sandbox_id,
                    retain_on_close=self.retain_sandboxes,
                )

            try:
                # Establish the complete fixed pool before any worker dequeues
                # a second problem.  Without this rendezvous, a fast worker can
                # consume multiple items while slower sandboxes are still being
                # created, reducing the requested active concurrency and making
                # reuse distribution nondeterministic.
                try:
                    session = open_worker_session(assigned_id)
                    current_id = getattr(session, "sandbox_id", None)
                    if current_id != assigned_id:
                        self._pool_replace(assigned_id, current_id)
                    assigned_id = current_id
                except BaseException as exc:  # noqa: BLE001
                    if isinstance(exc, (KeyboardInterrupt, SystemExit)):
                        raise
                    # Participate in the barrier even if initial creation
                    # failed; the ordinary per-item path retries creation and
                    # records a bounded infrastructure result if it still fails.
                    session = None
                    self._pool_replace(assigned_id, None)
                    assigned_id = None
                try:
                    # Prefer a full fixed pool, but do not let one slow
                    # control-plane create/retry stall every healthy sandbox.
                    start_barrier.wait(timeout=30.0)
                except threading.BrokenBarrierError:
                    pass
                while True:
                    try:
                        item = work.get_nowait()
                    except queue.Empty:
                        return
                    started = time.monotonic()
                    try:
                        if session is None:
                            session = open_worker_session(None)
                            assigned_id = getattr(session, "sandbox_id", None)
                            self._pool_replace(None, assigned_id)
                        result = session.run(
                            problem=item.problem,
                            timeout_seconds=self.timeout_seconds,
                        )
                    except BaseException as exc:  # noqa: BLE001
                        if isinstance(exc, (KeyboardInterrupt, SystemExit)):
                            raise
                        result = _exception_result(exc, item, started)
                        if session is not None:
                            try:
                                session.discard()
                            except Exception:
                                _close_session_quietly(session)
                            self._pool_replace(assigned_id, None)
                            assigned_id = None
                            session = None
                    finally:
                        work.task_done()
                    completed.put(
                        BatchRunRecord(
                            input_line=item.input_line,
                            result=result,
                        )
                    )
            finally:
                if release_barrier is not None:
                    try:
                        release_barrier.wait()
                    except threading.BrokenBarrierError:
                        pass
                if session is not None:
                    _close_session_quietly(session)
                    if not self.retain_sandboxes:
                        self._pool_replace(assigned_id, None)

        with ThreadPoolExecutor(
            max_workers=worker_count,
            thread_name_prefix="solver-sandbox-pool",
        ) as executor:
            futures = [executor.submit(worker, i) for i in range(worker_count)]
            for _ in items:
                yield completed.get()
            for future in futures:
                future.result()


def _exception_result(
    exc: BaseException,
    item: ProblemItem,
    started: float,
) -> SandboxRunResult:
    create_attempts = int(getattr(exc, "create_attempts", 0))
    create_errors = getattr(exc, "create_errors", [])
    create_elapsed_seconds = float(getattr(exc, "create_elapsed_seconds", 0.0))
    display_error = getattr(exc, "display_error", f"{type(exc).__name__}: {exc}")
    return SandboxRunResult(
        run_id=uuid.uuid4().hex,
        sandbox_id=None,
        problem_id=item.problem.id,
        status="infrastructure_error",
        solved=False,
        create_attempts=create_attempts,
        create_errors=create_errors,
        create_elapsed_seconds=create_elapsed_seconds,
        elapsed_seconds=round(time.monotonic() - started, 3),
        error=display_error[:4000],
    )


def iter_problems_jsonl(lines: Iterable[str]) -> Iterator[ProblemItem]:
    for line_number, raw_line in enumerate(lines, start=1):
        line = raw_line.strip()
        if not line:
            continue
        try:
            payload = json.loads(line)
            problem = Stage2Problem.model_validate(payload)
        except (json.JSONDecodeError, ValidationError) as exc:
            raise ValueError(f"invalid problem JSONL at line {line_number}: {exc}") from exc
        yield ProblemItem(input_line=line_number, problem=problem)
