from __future__ import annotations

import argparse
import ctypes
import json
import os
import signal
import subprocess
import sys
import threading
import time
from pathlib import Path


def _read_int(path: Path) -> int | None:
    try:
        text = path.read_text(encoding="ascii").strip()
        return None if text == "max" else int(text)
    except (OSError, ValueError):
        return None


def _status_kib(pid: int, field: str) -> int | None:
    try:
        with Path(f"/proc/{pid}/status").open("r", encoding="ascii") as handle:
            for line in handle:
                if line.startswith(field + ":"):
                    return int(line.split()[1])
    except (OSError, ValueError, IndexError):
        return None
    return None


def _children(pid: int) -> set[int]:
    found: set[int] = set()
    task_dir = Path(f"/proc/{pid}/task")
    try:
        tasks = list(task_dir.iterdir())
    except OSError:
        return found
    for task in tasks:
        try:
            text = (task / "children").read_text(encoding="ascii")
        except OSError:
            continue
        for token in text.split():
            try:
                found.add(int(token))
            except ValueError:
                pass
    return found


def _process_tree(root_pid: int) -> set[int]:
    seen: set[int] = set()
    pending = [root_pid]
    while pending:
        pid = pending.pop()
        if pid in seen:
            continue
        seen.add(pid)
        pending.extend(_children(pid) - seen)
    return seen


def _process_tree_memory(root_pid: int) -> tuple[int | None, int | None, int]:
    rss_total = 0
    hwm_total = 0
    rss_seen = 0
    hwm_seen = 0
    alive = 0
    for pid in _process_tree(root_pid):
        rss = _status_kib(pid, "VmRSS")
        hwm = _status_kib(pid, "VmHWM")
        if rss is not None:
            rss_total += rss * 1024
            rss_seen += 1
            alive += 1
        if hwm is not None:
            hwm_total += hwm * 1024
            hwm_seen += 1
    return (
        rss_total if rss_seen else None,
        hwm_total if hwm_seen else None,
        alive,
    )


def _cgroup_info() -> tuple[str, Path] | None:
    try:
        lines = Path("/proc/self/cgroup").read_text(encoding="ascii").splitlines()
    except OSError:
        return None
    for line in lines:
        parts = line.split(":", 2)
        if len(parts) == 3 and parts[0] == "0":
            relative = parts[2].lstrip("/")
            return "v2", Path("/sys/fs/cgroup") / relative
    for line in lines:
        parts = line.split(":", 2)
        if len(parts) != 3 or "memory" not in parts[1].split(","):
            continue
        relative = parts[2].lstrip("/")
        for base in (Path("/sys/fs/cgroup/memory"), Path("/sys/fs/cgroup")):
            candidate = base / relative
            if candidate.exists():
                return "v1", candidate
    return None


def _memory_events(cgroup: tuple[str, Path] | None) -> dict[str, int]:
    if cgroup is None:
        return {}
    version, path = cgroup
    if version == "v1":
        failcnt = _read_int(path / "memory.failcnt")
        return {"failcnt": failcnt} if failcnt is not None else {}
    result: dict[str, int] = {}
    try:
        lines = (path / "memory.events").read_text(encoding="ascii").splitlines()
    except OSError:
        return result
    for line in lines:
        parts = line.split()
        if len(parts) == 2:
            try:
                result[parts[0]] = int(parts[1])
            except ValueError:
                pass
    return result


def _atomic_json(path: Path, payload: dict) -> None:
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    temporary.write_text(
        json.dumps(payload, ensure_ascii=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def _set_parent_death_signal() -> None:
    try:
        libc = ctypes.CDLL(None)
        libc.prctl(1, signal.SIGKILL)
    except Exception:
        pass


def _relay_stdin(child: subprocess.Popen[str]) -> None:
    """Forward the envd command stream to the supervised solver."""

    assert child.stdin is not None
    try:
        for line in sys.stdin:
            child.stdin.write(line)
            child.stdin.flush()
    except (BrokenPipeError, OSError, ValueError):
        pass
    finally:
        try:
            child.stdin.close()
        except (BrokenPipeError, OSError, ValueError):
            pass


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--solver", type=Path, required=True)
    parser.add_argument("--metrics", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=float, required=True)
    parser.add_argument("--first-window-seconds", type=float, default=300.0)
    parser.add_argument("--sample-interval", type=float, default=0.25)
    parser.add_argument("--series-interval", type=float, default=1.0)
    parser.add_argument("--memory-limit-bytes", type=int)
    args = parser.parse_args()

    if args.memory_limit_bytes is not None and args.memory_limit_bytes <= 0:
        parser.error("--memory-limit-bytes must be positive")

    child = subprocess.Popen(
        [sys.executable, "-B", "-u", str(args.solver)],
        stdin=subprocess.PIPE,
        stdout=sys.stdout,
        stderr=sys.stderr,
        text=True,
        encoding="utf-8",
        preexec_fn=_set_parent_death_signal,
    )
    threading.Thread(
        target=_relay_stdin,
        args=(child,),
        name="solver-stdin-relay",
        daemon=True,
    ).start()
    started = time.monotonic()
    cgroup = _cgroup_info()
    cgroup_version = cgroup[0] if cgroup else None
    cgroup_path = cgroup[1] if cgroup else None
    if cgroup_version == "v2" and cgroup_path:
        cgroup_limit = _read_int(cgroup_path / "memory.max")
    elif cgroup_version == "v1" and cgroup_path:
        cgroup_limit = _read_int(cgroup_path / "memory.limit_in_bytes")
    else:
        cgroup_limit = None
    events_start = _memory_events(cgroup)
    received_signal: int | None = None

    def request_stop(signum: int, _frame: object) -> None:
        nonlocal received_signal
        received_signal = signum

    signal.signal(signal.SIGTERM, request_stop)
    signal.signal(signal.SIGINT, request_stop)

    peak_rss_first: int | None = None
    peak_rss_full: int | None = None
    peak_hwm_full: int | None = None
    peak_cgroup_first: int | None = None
    peak_cgroup_full: int | None = None
    sample_count = 0
    series: list[list[float | int | None]] = []
    next_series = 0.0
    stop_reason = "running"
    child_exit_code: int | None = None

    def sample(final: bool = False) -> None:
        nonlocal peak_rss_first, peak_rss_full, peak_hwm_full
        nonlocal peak_cgroup_first, peak_cgroup_full, sample_count, next_series
        elapsed = max(0.0, time.monotonic() - started)
        rss, hwm, alive = _process_tree_memory(child.pid)
        if cgroup_version == "v2" and cgroup_path:
            cgroup_current = _read_int(cgroup_path / "memory.current")
        elif cgroup_version == "v1" and cgroup_path:
            cgroup_current = _read_int(cgroup_path / "memory.usage_in_bytes")
        else:
            cgroup_current = None
        if rss is not None:
            peak_rss_full = rss if peak_rss_full is None else max(peak_rss_full, rss)
            if elapsed <= args.first_window_seconds:
                peak_rss_first = rss if peak_rss_first is None else max(peak_rss_first, rss)
        if hwm is not None:
            peak_hwm_full = hwm if peak_hwm_full is None else max(peak_hwm_full, hwm)
        if cgroup_current is not None:
            peak_cgroup_full = (
                cgroup_current if peak_cgroup_full is None else max(peak_cgroup_full, cgroup_current)
            )
            if elapsed <= args.first_window_seconds:
                peak_cgroup_first = (
                    cgroup_current
                    if peak_cgroup_first is None
                    else max(peak_cgroup_first, cgroup_current)
                )
        sample_count += 1
        if final or elapsed + 1e-9 >= next_series:
            series.append([round(elapsed, 3), rss, cgroup_current, alive])
            next_series = elapsed + args.series_interval
        events_now = _memory_events(cgroup)
        payload = {
            "schema_version": 2,
            "sample_interval_seconds": args.sample_interval,
            "series_interval_seconds": args.series_interval,
            "first_window_seconds": args.first_window_seconds,
            "budget_seconds": args.timeout_seconds,
            "monitor_elapsed_seconds": round(elapsed, 3),
            "sample_count": sample_count,
            "process_tree_peak_rss_first_window_bytes": peak_rss_first,
            "process_tree_peak_rss_full_bytes": peak_rss_full,
            "process_tree_peak_hwm_full_bytes": peak_hwm_full,
            "sandbox_cgroup_peak_current_first_window_bytes": peak_cgroup_first,
            "sandbox_cgroup_peak_current_full_bytes": peak_cgroup_full,
            "sandbox_cgroup_memory_max_bytes": cgroup_limit,
            "solver_memory_limit_bytes": args.memory_limit_bytes,
            "sandbox_cgroup_version": cgroup_version,
            "memory_events_start": events_start,
            "memory_events_current": events_now,
            "memory_events_delta": {
                key: events_now.get(key, 0) - events_start.get(key, 0)
                for key in set(events_start) | set(events_now)
            },
            "stop_reason": stop_reason,
            "child_exit_code": child_exit_code,
            "final": final,
            "samples": series,
        }
        _atomic_json(args.metrics, payload)

    while True:
        sample()
        child_exit_code = child.poll()
        if child_exit_code is not None:
            stop_reason = "child_exit"
            break
        if (
            args.memory_limit_bytes is not None
            and peak_rss_full is not None
            and peak_rss_full > args.memory_limit_bytes
        ):
            # Enforce the user-visible resident-memory ceiling across the
            # complete solver process tree.  RLIMIT_AS is intentionally not
            # used: virtual address space includes non-resident mappings and
            # is not the stated 1400 MiB physical-memory metric.
            stop_reason = "memory_limit"
            child.kill()
            break
        elapsed = time.monotonic() - started
        if received_signal is not None:
            stop_reason = f"signal_{received_signal}"
            child.terminate()
            break
        if elapsed >= args.timeout_seconds:
            stop_reason = "budget_timeout"
            child.terminate()
            break
        time.sleep(args.sample_interval)

    if child.poll() is None:
        try:
            child.wait(timeout=2.0)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait(timeout=2.0)
    child_exit_code = child.returncode
    sample(final=True)
    if stop_reason == "budget_timeout":
        return 124
    if stop_reason == "memory_limit":
        return 125
    if received_signal is not None:
        return 128 + received_signal
    return int(child_exit_code or 0)


if __name__ == "__main__":
    raise SystemExit(main())
