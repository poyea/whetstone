#!/usr/bin/env python3
"""Run whetstone on all .cnf benchmarks and produce a results table."""

import argparse
import glob
import os
import re
import subprocess
import sys
import time


def find_binary():
    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(script_dir)

    candidates = [
        os.path.join(repo_root, "build", "whetstone"),
        os.path.join(repo_root, "build", "whetstone.exe"),
        os.path.join(repo_root, "build", "Release", "whetstone.exe"),
        os.path.join(repo_root, "build", "Debug", "whetstone.exe"),
    ]

    for c in candidates:
        if os.path.isfile(c):
            return c

    return None


def parse_stats(stderr_output):
    stats = {}
    for line in stderr_output.splitlines():
        m = re.match(r"c\s+(\w+):\s+(\d+)", line)
        if m:
            stats[m.group(1)] = int(m.group(2))
    return stats


def run_benchmark(binary, cnf_path, timeout, extra_args=None):
    cmd = [binary, cnf_path]
    if extra_args:
        cmd.extend(extra_args)

    start = time.perf_counter()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        elapsed = time.perf_counter() - start

        answer = "?"
        for line in result.stdout.splitlines():
            if line.startswith("s "):
                answer = "SAT" if "SATISFIABLE" == line.split()[-1] else "UNSAT"
                break

        stats = parse_stats(result.stderr)
        return {
            "answer": answer,
            "time": elapsed,
            "conflicts": stats.get("conflicts", 0),
            "decisions": stats.get("decisions", 0),
            "propagations": stats.get("propagations", 0),
            "restarts": stats.get("restarts", 0),
        }
    except subprocess.TimeoutExpired:
        return {"answer": "TIMEOUT", "time": timeout}


def format_num(n):
    if n >= 1_000_000:
        return f"{n / 1_000_000:.1f}M"
    if n >= 1_000:
        return f"{n / 1_000:.1f}K"
    return str(n)


def main():
    parser = argparse.ArgumentParser(description="Run whetstone benchmarks")
    parser.add_argument("--binary", help="Path to whetstone binary")
    parser.add_argument("--timeout", type=float, default=30.0, help="Timeout per instance (seconds)")
    parser.add_argument("--dir", help="Directory with .cnf files")
    parser.add_argument("--compare", action="store_true", help="Run both glucose and luby, compare")
    args = parser.parse_args()

    binary = args.binary or find_binary()
    if not binary:
        print("error: cannot find whetstone binary. Build first or pass --binary.")
        sys.exit(1)

    print(f"binary: {binary}")
    print(f"timeout: {args.timeout}s\n")

    bench_dir = args.dir or os.path.dirname(os.path.abspath(__file__))
    cnf_files = sorted(glob.glob(os.path.join(bench_dir, "*.cnf")))

    if not cnf_files:
        print("no .cnf files found. Run generate.py first.")
        sys.exit(1)

    if args.compare:
        run_comparison(binary, cnf_files, args.timeout)
    else:
        run_single(binary, cnf_files, args.timeout)


def run_single(binary, cnf_files, timeout):
    hdr = f"{'benchmark':<40} {'answer':>7} {'time':>8} {'confl':>8} {'dec':>8} {'prop':>10} {'rst':>6}"
    sep = "-" * len(hdr)
    print(hdr)
    print(sep)

    total_time = 0
    solved = 0

    for cnf in cnf_files:
        name = os.path.basename(cnf)
        r = run_benchmark(binary, cnf, timeout)

        if r["answer"] == "TIMEOUT":
            print(f"{name:<40} {'TO':>7} {r['time']:>7.1f}s")
        else:
            solved += 1
            total_time += r["time"]
            print(
                f"{name:<40} {r['answer']:>7} {r['time']:>7.3f}s "
                f"{format_num(r['conflicts']):>8} "
                f"{format_num(r['decisions']):>8} "
                f"{format_num(r['propagations']):>10} "
                f"{r['restarts']:>6}"
            )

    print(sep)
    print(f"solved: {solved}/{len(cnf_files)}  total time: {total_time:.3f}s")


def run_comparison(binary, cnf_files, timeout):
    hdr = (
        f"{'benchmark':<35} {'answer':>7} "
        f"{'glucose':>9} {'g.confl':>8} "
        f"{'luby':>9} {'l.confl':>8} "
        f"{'speedup':>8}"
    )
    sep = "-" * len(hdr)
    print(hdr)
    print(sep)

    g_total = 0
    l_total = 0

    for cnf in cnf_files:
        name = os.path.basename(cnf)

        rg = run_benchmark(binary, cnf, timeout, ["--glucose"])
        rl = run_benchmark(binary, cnf, timeout, ["--luby"])

        gt = rg["time"] if rg["answer"] != "TIMEOUT" else float("inf")
        lt = rl["time"] if rl["answer"] != "TIMEOUT" else float("inf")

        g_total += min(gt, timeout)
        l_total += min(lt, timeout)

        def fmt_time(r):
            return "TO" if r["answer"] == "TIMEOUT" else f"{r['time']:.3f}s"

        def fmt_confl(r):
            return "-" if r["answer"] == "TIMEOUT" else format_num(r.get("conflicts", 0))

        speedup = ""
        if gt < float("inf") and lt < float("inf") and gt > 0:
            ratio = lt / gt
            speedup = f"{ratio:.2f}x"

        answer = rg["answer"] if rg["answer"] != "TIMEOUT" else rl["answer"]

        print(
            f"{name:<35} {answer:>7} "
            f"{fmt_time(rg):>9} {fmt_confl(rg):>8} "
            f"{fmt_time(rl):>9} {fmt_confl(rl):>8} "
            f"{speedup:>8}"
        )

    print(sep)
    print(f"total  glucose: {g_total:.3f}s  luby: {l_total:.3f}s")


if __name__ == "__main__":
    main()
