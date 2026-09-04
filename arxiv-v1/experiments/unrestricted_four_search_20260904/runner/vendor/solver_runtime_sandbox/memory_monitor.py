from __future__ import annotations

import argparse
import ctypes
import json
import os
import signal
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
    try:
        tasks = list(Path(f"/proc/{pid}/task").iterdir())
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
    return rss_total if rss_seen else None, hwm_total if hwm_seen else None, alive


def _atomic_json(path: Path, payload: dict) -> None:
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    temporary.write_text(
        json.dumps(payload, ensure_ascii=False, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def _set_parent_death_signal() -> None:
    try:
        ctypes.CDLL(None).prctl(1, signal.SIGKILL)
    except Exception:
        pass


def _kill_tree(root_pid: int) -> None:
    # Descendants first, then the protocol-facing solver process.
    for pid in sorted(_process_tree(root_pid), reverse=True):
        try:
            os.kill(pid, signal.SIGKILL)
        except (OSError, ProcessLookupError):
            pass


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pid", type=int, required=True)
    parser.add_argument("--metrics", type=Path, required=True)
    parser.add_argument("--timeout-seconds", type=float, required=True)
    parser.add_argument("--first-window-seconds", type=float, default=300.0)
    parser.add_argument("--sample-interval", type=float, default=0.05)
    parser.add_argument("--series-interval", type=float, default=1.0)
    parser.add_argument("--memory-limit-bytes", type=int)
    args = parser.parse_args()
    if args.pid <= 0:
        parser.error("--pid must be positive")
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    if args.sample_interval <= 0 or args.series_interval <= 0:
        parser.error("sampling intervals must be positive")
    if args.memory_limit_bytes is not None and args.memory_limit_bytes <= 0:
        parser.error("--memory-limit-bytes must be positive")

    _set_parent_death_signal()
    started = time.monotonic()
    received_signal: int | None = None

    def request_stop(signum: int, _frame: object) -> None:
        nonlocal received_signal
        received_signal = signum

    signal.signal(signal.SIGTERM, request_stop)
    signal.signal(signal.SIGINT, request_stop)

    peak_rss_first: int | None = None
    peak_rss_full: int | None = None
    peak_hwm_full: int | None = None
    sample_count = 0
    series: list[list[float | int | None]] = []
    next_series = 0.0
    stop_reason = "running"

    def sample(*, final: bool = False) -> tuple[int | None, int]:
        nonlocal peak_rss_first, peak_rss_full, peak_hwm_full
        nonlocal sample_count, next_series
        elapsed = max(0.0, time.monotonic() - started)
        rss, hwm, alive = _process_tree_memory(args.pid)
        if rss is not None:
            peak_rss_full = rss if peak_rss_full is None else max(peak_rss_full, rss)
            if elapsed <= args.first_window_seconds:
                peak_rss_first = rss if peak_rss_first is None else max(peak_rss_first, rss)
        if hwm is not None:
            peak_hwm_full = hwm if peak_hwm_full is None else max(peak_hwm_full, hwm)
        sample_count += 1
        if final or elapsed + 1e-9 >= next_series:
            series.append([round(elapsed, 3), rss, alive])
            next_series = elapsed + args.series_interval
        _atomic_json(
            args.metrics,
            {
                "schema_version": 3,
                "target_pid": args.pid,
                "sample_interval_seconds": args.sample_interval,
                "series_interval_seconds": args.series_interval,
                "first_window_seconds": args.first_window_seconds,
                "budget_seconds": args.timeout_seconds,
                "monitor_elapsed_seconds": round(elapsed, 3),
                "sample_count": sample_count,
                "process_tree_peak_rss_first_window_bytes": peak_rss_first,
                "process_tree_peak_rss_full_bytes": peak_rss_full,
                "process_tree_peak_hwm_full_bytes": peak_hwm_full,
                "solver_memory_limit_bytes": args.memory_limit_bytes,
                "stop_reason": stop_reason,
                "final": final,
                "samples": series,
            },
        )
        return rss, alive

    while True:
        rss, alive = sample()
        if alive == 0:
            stop_reason = "solver_exit"
            break
        if received_signal is not None:
            stop_reason = f"signal_{received_signal}"
            break
        if args.memory_limit_bytes is not None and rss is not None and rss > args.memory_limit_bytes:
            stop_reason = "memory_limit"
            _kill_tree(args.pid)
            break
        if time.monotonic() - started >= args.timeout_seconds:
            stop_reason = "monitor_timeout"
            break
        time.sleep(args.sample_interval)

    sample(final=True)
    return 125 if stop_reason == "memory_limit" else 0


if __name__ == "__main__":
    raise SystemExit(main())
