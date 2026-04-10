#!/usr/bin/env python3
"""Generate PDF comparing Loom2 Velvet, Loom Velvet, and Dafny verification times."""

import csv
import subprocess
import sys
import time
from pathlib import Path

import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.backends.backend_pdf as pdf_backend
import numpy as np

CSV_PATH = Path("/Users/volodeyka/Desktop/NUS/Lean/Loom/Code/CaseStudies/Velvet/Bench/results/benchmark_results.csv")
THEBES = Path("/Users/volodeyka/conductor/workspaces/loom2/thebes")
BENCH_DIR = THEBES / "Loom" / "Test" / "Velvet" / "Bench"
OUTPUT_PATH = Path("/Users/volodeyka/Desktop/benchmark_comparison.pdf")

# Map CSV short names to our file names
NAME_MAP = {
    "consecNums": "ContainsConsecutiveNumbers",
    "countSumDiv": "CountSumDivisibleBy",
    "cubeElements": "CubeElements",
    "cubeSurfaceArea": "CubeSurfaceArea",
    "differenceMinMax": "DifferenceMinMax",
    "elementWiseModulo": "ElementWiseModulo",
    "findSmallest": "FindSmallest",
    "hasOppositeSign": "HasOppositeSign",
    "isDivisibleBy11": "IsDivisibleBy11",
    "isEven": "IsEven",
    "isGreater": "IsGreater",
    "isPrime": "IsPrime",
    "kthElement": "KthElement",
    "lastDigit": "LastDigit",
    "minOfThree": "MinOfThree",
    "multiply": "Multiply",
    "myMin": "MyMin",
    "removeElement": "RemoveElement",
    "sumAndAverage": "SumAndAverage",
    "sumOfSquaresOfOdd": "SumOfSquaresOfFirstNOddNumbers",
    "swapFirstAndLast": "SwapFirstAndLast",
    "findEvenNumbers": "FindEvenNumbers",
    "findMajorityElement": "FindMajorityElement",
    "ifPowerOfFour": "IfPowerOfFour",
    "isSorted": "IsSorted",
    "isSublist": "IsSublist",
    "mergeSorted": "MergeSorted",
}

DISPLAY = {
    "ContainsConsecutiveNumbers": "ConsecNums",
    "CountSumDivisibleBy": "CountSumDiv",
    "CubeElements": "CubeElem",
    "CubeSurfaceArea": "CubeSurf",
    "DifferenceMinMax": "DiffMinMax",
    "ElementWiseModulo": "ElemMod",
    "FindSmallest": "FindSmall",
    "HasOppositeSign": "OppSign",
    "IsDivisibleBy11": "DivBy11",
    "IsEven": "IsEven",
    "IsGreater": "IsGreater",
    "IsPrime": "IsPrime",
    "KthElement": "KthElem",
    "LastDigit": "LastDigit",
    "MinOfThree": "MinOf3",
    "Multiply": "Multiply",
    "MyMin": "MyMin",
    "RemoveElement": "RemoveElem",
    "SumAndAverage": "SumAvg",
    "SumOfSquaresOfFirstNOddNumbers": "SumSqOdd",
    "SwapFirstAndLast": "SwapFL",
    "FindEvenNumbers": "FindEven",
    "FindMajorityElement": "FindMajority",
    "IfPowerOfFour": "PowOf4",
    "IsSorted": "IsSorted",
    "IsSublist": "IsSublist",
    "MergeSorted": "MergeSorted",
}

def measure_loom2():
    """Measure loom2 verification times (fresh, no cache)."""
    results = {}
    files = sorted(BENCH_DIR.glob("*.lean"))
    skip = {"All", "MinReprSymSimp", "Profile", "ExpensiveGoals"}
    for f in files:
        name = f.stem
        if name in skip:
            continue
        print(f"  Measuring {name}...", end=" ", flush=True)
        start = time.perf_counter()
        r = subprocess.run(
            ["lake", "env", "lean", str(f)],
            capture_output=True, text=True, timeout=120,
            cwd=str(THEBES)
        )
        elapsed = time.perf_counter() - start
        ok = r.returncode == 0
        status = "ok" if ok else "FAIL"
        print(f"{elapsed:.2f}s ({status})")
        results[name] = elapsed if ok else None
    return results


def main():
    print("Measuring loom2 times (fresh build)...")
    loom2 = measure_loom2()

    # Read CSV
    csv_data = {}
    with open(CSV_PATH) as f:
        reader = csv.DictReader(f)
        for row in reader:
            our_name = NAME_MAP.get(row["program"])
            if our_name:
                csv_data[our_name] = {
                    "folder": row["folder"],
                    "dafny": float(row["dafny_mean"]),
                    "loom": float(row["lean_mean"]),
                }

    # Build entries
    entries = []
    for name, csv_row in csv_data.items():
        entries.append({
            "name": name,
            "display": DISPLAY.get(name, name),
            "folder": csv_row["folder"],
            "dafny": csv_row["dafny"],
            "loom": csv_row["loom"],
            "loom2": loom2.get(name),
        })

    entries.sort(key=lambda e: e["dafny"])

    # Clip outliers at 7s
    CLIP = 7.0

    fig, ax = plt.subplots(figsize=(18, 6))

    names = [e["display"] for e in entries]
    dafny = [min(e["dafny"], CLIP) for e in entries]
    loom = [min(e["loom"], CLIP) for e in entries]
    loom2_vals = [min(e["loom2"], CLIP) if e["loom2"] is not None else 0 for e in entries]

    x = np.arange(len(names))
    width = 0.25

    ax.bar(x - width, dafny, width, label='Dafny', color='#3498db',
           edgecolor='black', linewidth=0.5)
    ax.bar(x, loom, width, label='Loom Velvet', color='#e67e22',
           edgecolor='black', linewidth=0.5)

    colors = ['#2ecc71' if e["loom2"] is not None else '#e74c3c' for e in entries]
    ax.bar(x + width, loom2_vals, width, label='Loom2 Velvet', color=colors,
           edgecolor='black', linewidth=0.5)

    # Mark clipped bars
    for i, e in enumerate(entries):
        if e["dafny"] > CLIP:
            ax.text(x[i] - width, CLIP + 0.05, f'{e["dafny"]:.1f}', ha='center', va='bottom', fontsize=6, color='#3498db')
        if e["loom"] > CLIP:
            ax.text(x[i], CLIP + 0.05, f'{e["loom"]:.1f}', ha='center', va='bottom', fontsize=6, color='#e67e22')
        if e["loom2"] is not None and e["loom2"] > CLIP:
            ax.text(x[i] + width, CLIP + 0.05, f'{e["loom2"]:.1f}', ha='center', va='bottom', fontsize=6, color='#2ecc71')
        if e["loom2"] is None:
            ax.text(x[i] + width, 0.05, 'X', ha='center', va='bottom', fontsize=8, color='red', fontweight='bold')

    # Shade folders
    both_easy_end = sum(1 for e in entries if e["folder"] == "both_easy")
    ax.axvspan(-0.5, both_easy_end - 0.5, alpha=0.05, color='blue')
    ax.axvspan(both_easy_end - 0.5, len(entries) - 0.5, alpha=0.05, color='red')
    ax.text(both_easy_end / 2 - 0.5, CLIP * 0.95, 'easy', ha='center', fontsize=10, fontstyle='italic', alpha=0.5)
    ax.text((both_easy_end + len(entries)) / 2 - 0.5, CLIP * 0.95, 'needs proofs', ha='center', fontsize=10, fontstyle='italic', alpha=0.5)

    ax.set_ylabel('Verification Time (seconds)', fontsize=12)
    ax.set_title('Verification Time Comparison: Dafny vs Loom Velvet vs Loom2 Velvet\n(bars clipped at 7s, actual values annotated)',
                 fontsize=13, fontweight='bold')
    ax.set_xticks(x)
    ax.set_xticklabels(names, rotation=45, ha='right', fontsize=8)
    ax.set_ylim(0, CLIP + 0.5)
    ax.legend(fontsize=10, loc='upper left')
    ax.yaxis.grid(True, linestyle='--', alpha=0.5)
    ax.set_axisbelow(True)

    plt.tight_layout()

    with pdf_backend.PdfPages(str(OUTPUT_PATH)) as pp:
        pp.savefig(fig, bbox_inches='tight')
    plt.close(fig)

    print(f"\nPDF saved to: {OUTPUT_PATH}")

if __name__ == "__main__":
    main()
