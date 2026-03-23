#!/usr/bin/env python3
"""Benchmark harness for Loom. Runs benchmarks, parses timing output, generates PDF plots."""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
RESULTS_DIR = PROJECT_ROOT / "bench" / "results"

BENCHMARKS = [
    "AddSubCancel",
    "AddSubCancelDeep",
    "AssertGadgetStep",
    "ConcreteEPostTwoPreds",
    "ConcretePostEPost",
    "DiteSplit",
    "DiteSplitReduce",
    "IteSplitReduce",
    "GetThrowSet",
    "MatchSplit",
    "MatchSplitTest",
]

DEFAULT_SIZES = list(range(100, 1001, 100))

METRICS = [
    ("total_ms",       "Total"),
    ("vcgen_ms",       "VC Generation"),
    ("discharge_ms",   "Discharging"),
    ("instantiate_ms", "Instantiate"),
    ("share_ms",       "shareCommon"),
    ("kernel_ms",      "Kernel"),
    ("unfold_ms",      "Unfolding"),
    ("share_per_size",  "ShareCommon / Proof Size"),
    ("kernel_per_shared", "Kernel / Shared Proof Size"),
]


def parse_args():
    p = argparse.ArgumentParser(description="Loom benchmark harness")
    p.add_argument("--plot-only", action="store_true", help="Regenerate plots from existing data")
    p.add_argument("--save-baseline", action="store_true", help="Save current results as baseline")
    p.add_argument("--update-baseline", action="store_true", help="Alias for --save-baseline")
    p.add_argument("--filter", type=str, default=None, help="Only run benchmarks matching substring")
    p.add_argument("--sizes", type=str, default=None, help="Comma-separated sizes (default: 100,200,...,1000)")
    p.add_argument("--timeout", type=int, default=60, help="Per-size timeout in seconds (default: 60)")
    return p.parse_args()


def ensure_lake_build(benchmarks: list[str]):
    # Test modules aren't in the library root, so we must build each explicitly
    modules = [f"Loom.Test.{b}" for b in benchmarks]
    print(f"Building {len(modules)} benchmark modules...")
    result = subprocess.run(
        ["lake", "build"] + modules,
        cwd=str(PROJECT_ROOT),
        capture_output=True,
        text=True,
        timeout=600,
    )
    if result.returncode != 0:
        print(f"lake build failed:\n{result.stderr}")
        sys.exit(1)
    print("Build successful.")


def make_runner_file(bench_name: str, size: int) -> Path:
    content = (
        f"import Loom.Test.{bench_name}\n"
        f"set_option maxRecDepth 100000\n"
        f"set_option maxHeartbeats 0\n"
        f"#eval runTests [{size}]\n"
    )
    fd, path = tempfile.mkstemp(suffix=".lean", prefix=f"bench_{bench_name}_{size}_")
    with os.fdopen(fd, "w") as f:
        f.write(content)
    return Path(path)


def parse_output(size: int, stdout: str) -> dict:
    unfold_ms = None
    vcgen_ms = None
    num_vcs = None
    discharge_ms = None
    instantiate_ms = None
    share_ms = None
    kernel_ms = None
    proof_size = None
    proof_size_shared = None

    for line in stdout.strip().split("\n"):
        line = line.strip()

        m = re.match(r"time spent unfolding:\s+(\d+)\s+ms", line)
        if m:
            unfold_ms = int(m.group(1))
            continue

        # With discharge timing
        m = re.match(
            r"goal_(\d+):\s+(\d+)\s+ms,\s+(\d+)\s+VCs\s+by\s+.+?:\s+(\d+)\s+ms,\s+"
            r"instantiate:\s+(\d+)\s+ms,\s+shareCommon:\s+(\d+)\s+ms,\s+kernel:\s+(\d+)\s+ms"
            r"(?:,\s+proofSize:\s+(\d+))?"
            r"(?:,\s+proofSizeShared:\s+(\d+))?",
            line,
        )
        if m:
            vcgen_ms = int(m.group(2))
            num_vcs = int(m.group(3))
            discharge_ms = int(m.group(4))
            instantiate_ms = int(m.group(5))
            share_ms = int(m.group(6))
            kernel_ms = int(m.group(7))
            if m.group(8):
                proof_size = int(m.group(8))
            if m.group(9):
                proof_size_shared = int(m.group(9))
            continue

        # Without discharge timing (0 VCs)
        m = re.match(
            r"goal_(\d+):\s+(\d+)\s+ms,\s+(\d+)\s+VCs,\s+"
            r"instantiate:\s+(\d+)\s+ms,\s+shareCommon:\s+(\d+)\s+ms,\s+kernel:\s+(\d+)\s+ms"
            r"(?:,\s+proofSize:\s+(\d+))?"
            r"(?:,\s+proofSizeShared:\s+(\d+))?",
            line,
        )
        if m:
            vcgen_ms = int(m.group(2))
            num_vcs = int(m.group(3))
            discharge_ms = 0
            instantiate_ms = int(m.group(4))
            share_ms = int(m.group(5))
            kernel_ms = int(m.group(6))
            if m.group(7):
                proof_size = int(m.group(7))
            if m.group(8):
                proof_size_shared = int(m.group(8))
            continue

    if vcgen_ms is None:
        return {"size": size, "status": "parse_error", "raw_output": stdout[:1000]}

    total_ms = (unfold_ms or 0) + vcgen_ms + discharge_ms + instantiate_ms + share_ms + kernel_ms
    return {
        "size": size,
        "status": "ok",
        "unfold_ms": unfold_ms or 0,
        "vcgen_ms": vcgen_ms,
        "num_vcs": num_vcs,
        "discharge_ms": discharge_ms,
        "instantiate_ms": instantiate_ms,
        "share_ms": share_ms,
        "kernel_ms": kernel_ms,
        "total_ms": total_ms,
        "proof_size": proof_size or 0,
        "proof_size_shared": proof_size_shared or 0,
    }


def run_benchmark(bench_name: str, size: int, timeout: int) -> dict:
    tmp_path = make_runner_file(bench_name, size)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(tmp_path), "-Dwarn.sorry=false", "--tstack=100000000"],
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(PROJECT_ROOT),
        )
        if result.returncode != 0:
            err = (result.stderr or result.stdout)[:500].strip()
            return {"size": size, "status": "error", "error": err}
        return parse_output(size, result.stdout)
    except subprocess.TimeoutExpired:
        return {"size": size, "status": "timeout"}
    finally:
        tmp_path.unlink(missing_ok=True)


def run_all_benchmarks(benchmarks: list[str], sizes: list[int], timeout: int) -> dict:
    results = {}
    total = len(benchmarks) * len(sizes)
    done = 0

    for bench_name in benchmarks:
        print(f"\n=== {bench_name} ===")
        bench_results = []
        for size in sizes:
            done += 1
            print(f"  [{done}/{total}] n={size} ... ", end="", flush=True)
            result = run_benchmark(bench_name, size, timeout)
            bench_results.append(result)
            if result["status"] == "ok":
                print(f"vcgen={result['vcgen_ms']}ms total={result['total_ms']}ms")
            elif result["status"] == "error":
                print(f"ERROR: {result.get('error', '')[:200]}")
            else:
                print(result["status"])
        results[bench_name] = {"results": bench_results}

    return results


def save_results(benchmarks_data: dict):
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    git_commit = subprocess.run(
        ["git", "rev-parse", "--short", "HEAD"],
        capture_output=True, text=True, cwd=str(PROJECT_ROOT),
    ).stdout.strip()
    git_branch = subprocess.run(
        ["git", "branch", "--show-current"],
        capture_output=True, text=True, cwd=str(PROJECT_ROOT),
    ).stdout.strip()
    toolchain = ""
    tc_path = PROJECT_ROOT / "lean-toolchain"
    if tc_path.exists():
        toolchain = tc_path.read_text().strip()

    output = {
        "timestamp": datetime.now().isoformat(),
        "lean_toolchain": toolchain,
        "git_commit": git_commit,
        "git_branch": git_branch,
        "benchmarks": benchmarks_data,
    }
    path = RESULTS_DIR / "current.json"
    with open(path, "w") as f:
        json.dump(output, f, indent=2)
    print(f"\nResults saved to {path}")


def load_results(filename: str) -> dict | None:
    path = RESULTS_DIR / filename
    if not path.exists():
        return None
    with open(path) as f:
        return json.load(f)


def copy_current_to_baseline():
    src = RESULTS_DIR / "current.json"
    dst = RESULTS_DIR / "baseline.json"
    if not src.exists():
        print("No current.json found. Run benchmarks first.")
        sys.exit(1)
    shutil.copy2(str(src), str(dst))
    print(f"Baseline saved: {dst}")


COMPONENT_METRICS = [
    ("unfold_ms",      "Unfolding"),
    ("vcgen_ms",       "VC Generation"),
    ("discharge_ms",   "Discharging"),
    ("instantiate_ms", "Instantiate"),
    ("share_ms",       "shareCommon"),
    ("kernel_ms",      "Kernel"),
]

COMPONENT_COLORS = ["#4e79a7", "#f28e2b", "#e15759", "#76b7b2", "#59a14f", "#edc948"]


def generate_plots(results: dict, baseline: dict | None):
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        from matplotlib.backends.backend_pdf import PdfPages
    except ImportError:
        print("matplotlib not installed. Install with: pip install matplotlib")
        return

    benchmarks = results["benchmarks"]
    bench_names = sorted(benchmarks.keys())

    cmap = matplotlib.colormaps["tab10"]
    colors = {name: cmap(i) for i, name in enumerate(bench_names)}

    output_path = RESULTS_DIR / "plots.pdf"
    with PdfPages(str(output_path)) as pdf:
        # Page 1: metric comparison across benchmarks
        nmetrics = len(METRICS)
        ncols = 3
        nrows = (nmetrics + ncols - 1) // ncols
        fig, axes = plt.subplots(nrows, ncols, figsize=(18, 4 * nrows))
        axes = axes.flatten()

        title = f"Loom Benchmarks — {results.get('git_branch', '?')}@{results.get('git_commit', '?')}"
        if baseline:
            title += f" (baseline: {baseline.get('git_branch', '?')}@{baseline.get('git_commit', '?')})"
        fig.suptitle(title, fontsize=14)

        for idx, (metric_key, metric_label) in enumerate(METRICS):
            ax = axes[idx]
            ax.set_title(metric_label)
            ax.set_xlabel("Size (n)")
            # (numerator_key, denominator_key, multiplier, y_label)
            RATIO_METRICS = {
                "share_per_size":    ("share_ms",  "proof_size",        1_000_000, "μs per obj"),
                "kernel_per_shared": ("kernel_ms", "proof_size_shared", 1_000,     "ms per K objs"),
            }
            if metric_key in RATIO_METRICS:
                ax.set_ylabel(RATIO_METRICS[metric_key][3])
            else:
                ax.set_ylabel("Time (ms)")

            def get_values(ok_data, mkey):
                if mkey in RATIO_METRICS:
                    num_key, denom_key, mult, _ = RATIO_METRICS[mkey]
                    filtered = [d for d in ok_data if d.get(denom_key, 0) > 0]
                    sizes = [d["size"] for d in filtered]
                    values = [d[num_key] * mult / d[denom_key] for d in filtered]
                    return sizes, values
                else:
                    sizes = [d["size"] for d in ok_data]
                    values = [d.get(mkey, 0) for d in ok_data]
                    return sizes, values

            for bench_name in bench_names:
                data = benchmarks[bench_name]["results"]
                ok_data = [d for d in data if d.get("status") == "ok"]
                sizes, values = get_values(ok_data, metric_key)
                if values:
                    ax.plot(sizes, values, "o-", color=colors[bench_name],
                            label=bench_name, markersize=4)

            if baseline:
                for bench_name in bench_names:
                    if bench_name not in baseline.get("benchmarks", {}):
                        continue
                    data = baseline["benchmarks"][bench_name]["results"]
                    ok_data = [d for d in data if d.get("status") == "ok"]
                    sizes, values = get_values(ok_data, metric_key)
                    if values:
                        ax.plot(sizes, values, "--", color=colors[bench_name],
                                alpha=0.5, markersize=3)

            ax.grid(True, alpha=0.3)

        for idx in range(nmetrics, len(axes)):
            axes[idx].set_visible(False)

        handles, labels = axes[0].get_legend_handles_labels()
        if handles:
            fig.legend(handles, labels, loc="lower center",
                       ncol=min(len(bench_names), 6), fontsize=9,
                       bbox_to_anchor=(0.5, -0.02))

        plt.tight_layout(rect=[0, 0.04, 1, 0.96])
        pdf.savefig(fig, bbox_inches="tight")
        plt.close(fig)

        # Page 2: per-benchmark stacked area charts (component breakdown)
        ncols = 3
        nrows = (len(bench_names) + ncols - 1) // ncols
        fig, axes = plt.subplots(nrows, ncols, figsize=(18, 4 * nrows))
        if nrows == 1:
            axes = [axes]
        axes_flat = [ax for row in axes for ax in (row if hasattr(row, '__len__') else [row])]

        fig.suptitle("Component Breakdown per Benchmark", fontsize=14)

        for idx, bench_name in enumerate(bench_names):
            ax = axes_flat[idx]
            data = benchmarks[bench_name]["results"]
            ok_data = [d for d in data if d.get("status") == "ok"]
            if not ok_data:
                ax.set_visible(False)
                continue

            sizes = [d["size"] for d in ok_data]
            stacks = []
            labels = []
            for metric_key, metric_label in COMPONENT_METRICS:
                stacks.append([d.get(metric_key, 0) for d in ok_data])
                labels.append(metric_label)

            ax.stackplot(sizes, *stacks, labels=labels, colors=COMPONENT_COLORS, alpha=0.85)
            ax.set_title(bench_name)
            ax.set_xlabel("Size (n)")
            ax.set_ylabel("Time (ms)")
            ax.grid(True, alpha=0.3)

        for idx in range(len(bench_names), len(axes_flat)):
            axes_flat[idx].set_visible(False)

        # Shared legend from last visible plot
        handles, labels = axes_flat[0].get_legend_handles_labels()
        if handles:
            fig.legend(handles, labels, loc="lower center",
                       ncol=len(COMPONENT_METRICS), fontsize=9,
                       bbox_to_anchor=(0.5, -0.02))

        plt.tight_layout(rect=[0, 0.04, 1, 0.96])
        pdf.savefig(fig, bbox_inches="tight")
        plt.close(fig)

        # Page 3: per-benchmark proof size plots
        nrows3 = (len(bench_names) + ncols - 1) // ncols
        fig, axes = plt.subplots(nrows3, ncols, figsize=(18, 4 * nrows3))
        if nrows3 == 1:
            axes = [axes]
        axes_flat = [ax for row in axes for ax in (row if hasattr(row, '__len__') else [row])]
        fig.suptitle("Proof Size per Benchmark", fontsize=14)

        for idx, bench_name in enumerate(bench_names):
            ax = axes_flat[idx]
            data = benchmarks[bench_name]["results"]
            ok_data = [d for d in data if d.get("status") == "ok"]
            if not ok_data:
                ax.set_visible(False)
                continue

            sizes = [d["size"] for d in ok_data]
            values = [d.get("proof_size", 0) / 1_000 for d in ok_data]
            shared_values = [d.get("proof_size_shared", 0) / 1_000 for d in ok_data]
            ax.plot(sizes, values, "o-", color=colors[bench_name], markersize=4, label="before sharing")
            ax.plot(sizes, shared_values, "s-", color=colors[bench_name], markersize=4, alpha=0.6, label="after sharing")

            if baseline and bench_name in baseline.get("benchmarks", {}):
                bdata = baseline["benchmarks"][bench_name]["results"]
                bok = [d for d in bdata if d.get("status") == "ok"]
                bsizes = [d["size"] for d in bok]
                bvalues = [d.get("proof_size", 0) / 1_000 for d in bok]
                if bvalues:
                    ax.plot(bsizes, bvalues, "--", color=colors[bench_name],
                            alpha=0.5, markersize=3)

            ax.set_title(bench_name)
            ax.set_xlabel("Size (n)")
            ax.set_ylabel("Proof Size (K objs)")
            ax.legend(fontsize=7)
            ax.grid(True, alpha=0.3)

        for idx in range(len(bench_names), len(axes_flat)):
            axes_flat[idx].set_visible(False)

        plt.tight_layout(rect=[0, 0.02, 1, 0.96])
        pdf.savefig(fig, bbox_inches="tight")
        plt.close(fig)

    print(f"Plots saved to {output_path}")


def main():
    args = parse_args()

    if args.save_baseline or args.update_baseline:
        copy_current_to_baseline()
        return

    sizes = DEFAULT_SIZES
    if args.sizes:
        sizes = [int(s.strip()) for s in args.sizes.split(",")]

    benchmarks = BENCHMARKS
    if args.filter:
        benchmarks = [b for b in benchmarks if args.filter.lower() in b.lower()]
        if not benchmarks:
            print(f"No benchmarks match filter '{args.filter}'")
            sys.exit(1)

    if not args.plot_only:
        ensure_lake_build(benchmarks)
        results_data = run_all_benchmarks(benchmarks, sizes, args.timeout)
        save_results(results_data)
        results = load_results("current.json")
    else:
        results = load_results("current.json")
        if results is None:
            print("No current.json found. Run benchmarks first.")
            sys.exit(1)

    baseline = load_results("baseline.json")
    generate_plots(results, baseline)


if __name__ == "__main__":
    main()
