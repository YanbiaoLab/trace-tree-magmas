#!/usr/bin/env python3
"""Private unrestricted-search runner with explicit completion frames.

This adapter changes only two classifications required by the paper searches:

1. ``isolated_search_complete`` is a normal unsolved terminal outcome; and
2. a narrowly evidenced process-tree memory-limit kill is resource-censored,
   not an infrastructure failure.

The frozen runtime remains untouched.  This private adapter raises only its
in-process capture/protocol ceilings to the post-competition 1000 KiB contract.
"""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path


def locate_runner_root() -> Path:
    configured = os.environ.get("SOLVER_SANDBOX_RUNNER_ROOT")
    candidates = [Path(configured).expanduser()] if configured else []
    candidates.extend((Path.cwd(), Path(__file__).resolve().parent / "vendor"))
    for candidate in candidates:
        if (candidate / "solver_runtime_sandbox" / "runtime.py").is_file():
            return candidate.resolve()
    raise RuntimeError(
        "solver_runtime_sandbox not found; set SOLVER_SANDBOX_RUNNER_ROOT "
        "or run this adapter from the runner project root"
    )


RUNNER_ROOT = locate_runner_root()
sys.path.insert(0, str(RUNNER_ROOT))

from solver_runtime_sandbox.__main__ import main  # noqa: E402
import solver_runtime_sandbox.runtime as runtime_module  # noqa: E402
from solver_runtime_sandbox.runtime import SolverSandboxRuntime  # noqa: E402


UNRESTRICTED_CERTIFICATE_BYTES = 1_024_000
runtime_module.MAX_FALSE_CERT_BYTES = UNRESTRICTED_CERTIFICATE_BYTES
runtime_module.MAX_LEAN_CODE_BYTES = UNRESTRICTED_CERTIFICATE_BYTES
runtime_module.MAX_PROTOCOL_LINE_CHARS = 4 * 1024 * 1024


_ORIGINAL_HANDLE_LINE = SolverSandboxRuntime._handle_line
_ORIGINAL_RUN_ON_SANDBOX = SolverSandboxRuntime._run_on_sandbox


def _handle_line_with_isolated_completion(
    self,
    *,
    sandbox,
    command,
    state,
    line,
    judge_timeout_seconds,
):
    try:
        message = json.loads(line)
    except json.JSONDecodeError:
        message = None
    if isinstance(message, dict) and message.get("call") == "isolated_search_complete":
        terminal = message.get("terminal")
        if isinstance(terminal, dict):
            encoded = json.dumps(terminal, ensure_ascii=False, separators=(",", ":"))
            state.stderr_tail = (state.stderr_tail + encoded + "\n")[-200_000:]
        state.protocol_log.append("isolated_search_complete")
        return self._result(
            state,
            status="solver_exit",
            error="isolated search completed without an accepted candidate",
        )
    return _ORIGINAL_HANDLE_LINE(
        self,
        sandbox=sandbox,
        command=command,
        state=state,
        line=line,
        judge_timeout_seconds=judge_timeout_seconds,
    )


SolverSandboxRuntime._handle_line = _handle_line_with_isolated_completion


def _run_on_sandbox_with_memory_classification(self, **kwargs):
    result = _ORIGINAL_RUN_ON_SANDBOX(self, **kwargs)
    profile = result.memory_profile or {}
    explicit_limit = (
        result.status == "infrastructure_error"
        and profile.get("stop_reason") == "memory_limit"
    )
    limit_bytes = profile.get("solver_memory_limit_bytes")
    peak_bytes = profile.get("process_tree_peak_rss_full_bytes")
    inferred_external_limit = (
        result.status == "infrastructure_error"
        and profile.get("stop_reason") == "solver_exit"
        and isinstance(limit_bytes, (int, float))
        and isinstance(peak_bytes, (int, float))
        # The monitor samples, so it can miss the final allocation spike that
        # triggers the Sandbox cgroup kill.  A vanished PID plus a sampled peak
        # above 90% is sufficiently specific evidence of the configured cap.
        and peak_bytes >= 0.90 * limit_bytes
        and "process with pid" in str(result.error or "").lower()
        and "not found" in str(result.error or "").lower()
    )
    if explicit_limit or inferred_external_limit:
        limit_text = (
            f"{limit_bytes / 1048576:g} MiB"
            if isinstance(limit_bytes, (int, float))
            else "configured"
        )
        updated_profile = dict(profile)
        updated_profile["stop_reason"] = "memory_limit"
        return result.model_copy(
            update={
                "status": "solver_exit",
                "solved": False,
                "error": f"solver process tree reached the {limit_text} memory limit",
                "memory_profile": updated_profile,
            }
        )
    return result


SolverSandboxRuntime._run_on_sandbox = _run_on_sandbox_with_memory_classification


if __name__ == "__main__":
    main()
