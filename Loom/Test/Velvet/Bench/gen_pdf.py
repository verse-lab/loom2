#!/usr/bin/env python3
"""Generate a single-page PDF comparing Loom2 Velvet, Loom Velvet, and Dafny.
Style matches aggregate.py from the Velvet benchmark suite."""

import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import numpy as np

CSV_PATH = "/Users/volodeyka/Desktop/NUS/Lean/Loom/Code/CaseStudies/Velvet/Bench/results/benchmark_results.csv"

# Loom2 measured times (seconds, lake build with olean deleted to force re-elaboration)
loom2_data = {
    "ContainsConsecutiveNumbers": 0.762,
    "CountSumDivisibleBy": 0.676,
    "CubeElements": 0.683,
    "CubeSurfaceArea": 0.627,
    "DifferenceMinMax": 0.942,
    "ElementWiseModulo": 0.695,
    "FindEvenNumbers": 2.646,
    "FindMajorityElement": 0.889,
    "FindSmallest": 0.698,
    "HasOppositeSign": 0.635,
    "IfPowerOfFour": 0.763,
    "IsDivisibleBy11": 0.633,
    "IsEven": 0.655,
    "IsGreater": 0.700,
    "IsNonPrime": 0.691,
    "IsPrime": 0.721,
    "IsSorted": 0.781,
    "IsSublist": 0.697,
    "KthElement": 0.653,
    "LastDigit": 0.629,
    "MergeSorted": 2.890,
    "MinOfThree": 0.639,
    "Multiply": 0.617,
    "MyMin": 0.628,
    "RemoveElement": 0.762,
    "SumAndAverage": 0.660,
    "SumOfSquaresOfFirstNOddNumbers": 0.621,
    "SwapFirstAndLast": 0.655,
}

name_map = {
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

display_map = {
    "ContainsConsecutiveNumbers": "consecNums",
    "CountSumDivisibleBy": "countSumDiv",
    "CubeElements": "cubeElements",
    "CubeSurfaceArea": "cubeSurfaceArea",
    "DifferenceMinMax": "differenceMinMax",
    "ElementWiseModulo": "elementWiseModulo",
    "FindSmallest": "findSmallest",
    "HasOppositeSign": "hasOppositeSign",
    "IsDivisibleBy11": "isDivisibleBy11",
    "IsEven": "isEven",
    "IsGreater": "isGreater",
    "IsPrime": "isPrime",
    "KthElement": "kthElement",
    "LastDigit": "lastDigit",
    "MinOfThree": "minOfThree",
    "Multiply": "multiply",
    "MyMin": "myMin",
    "RemoveElement": "removeElement",
    "SumAndAverage": "sumAndAverage",
    "SumOfSquaresOfFirstNOddNumbers": "sumOfSquaresOfOdd",
    "SwapFirstAndLast": "swapFirstAndLast",
    "FindEvenNumbers": "findEvenNumbers",
    "FindMajorityElement": "findMajorityElement",
    "IfPowerOfFour": "ifPowerOfFour",
    "IsSorted": "isSorted",
    "IsSublist": "isSublist",
    "MergeSorted": "mergeSorted",
}

# Read CSV
csv_data = {}
with open(CSV_PATH) as f:
    reader = csv.DictReader(f)
    for row in reader:
        csv_name = row["program"]
        our_name = name_map.get(csv_name)
        if our_name:
            csv_data[our_name] = {
                "folder": row["folder"],
                "dafny": float(row["dafny_mean"]),
                "loom": float(row["lean_mean"]),
            }

# Build combined list: easy first, then hard, each sorted alphabetically
both_easy = []
needs_proofs = []

for our_name, csv_row in csv_data.items():
    entry = {
        "name": our_name,
        "display": display_map.get(our_name, our_name),
        "dafny": csv_row["dafny"],
        "loom": csv_row["loom"],
        "loom2": loom2_data.get(our_name, 0),
    }
    if csv_row["folder"] == "both_easy":
        both_easy.append(entry)
    else:
        needs_proofs.append(entry)

both_easy.sort(key=lambda e: e["display"])
needs_proofs.sort(key=lambda e: e["display"])
all_entries = both_easy + needs_proofs

# ── Chart (matching aggregate.py style exactly) ──────────────────────────────

plt.rcParams.update({
    "font.family": "sans-serif",
    "font.sans-serif": ["Inter", "Helvetica Neue", "Arial", "DejaVu Sans"],
})

n = len(all_entries)
names = [e["display"] for e in all_entries]
dafny = np.array([e["dafny"] for e in all_entries])
loom = np.array([e["loom"] for e in all_entries])
loom2 = np.array([e["loom2"] for e in all_entries])

# Colorblind-friendly palette (Paul Tol's bright scheme)
DAFNY_COLOR = "#4477AA"
LOOM_COLOR  = "#EE6677"
LOOM2_COLOR = "#228833"

# Velvet original uses 0.35 per program with 2 bars; we have 3 bars so use ~0.5
fig, ax = plt.subplots(figsize=(max(7, n * 0.58), 4))
fig.patch.set_facecolor("white")
ax.set_facecolor("white")

x = np.arange(n)
width = 0.18
gap = 0.03
label_fontsize = 5.5

y_max = float(max(dafny.max(), loom.max(), loom2.max()))
Y_CAP = 4.0 if y_max >= 4 else None

def clip(arr):
    return np.minimum(arr, Y_CAP) if Y_CAP else arr

common = dict(edgecolor="white", linewidth=0.5, zorder=3)
bars_d  = ax.bar(x - (width + gap), clip(dafny), width=width, label="Dafny",          color=DAFNY_COLOR, **common)
bars_l  = ax.bar(x,                  clip(loom),  width=width, label="Velvet",          color=LOOM_COLOR,  **common)
bars_l2 = ax.bar(x + (width + gap),  clip(loom2), width=width, label="Velvet (Loom2)",  color=LOOM2_COLOR, **common)

# Value labels + break marks
effective_cap = Y_CAP if Y_CAP else y_max
all_bars = [(bars_d, dafny), (bars_l, loom), (bars_l2, loom2)]

for i in range(n):
    for bars, vals in all_bars:
        bar = bars[i]
        val = vals[i]
        if val <= 0:
            continue
        clipped = Y_CAP is not None and val > Y_CAP
        bx = bar.get_x()
        bw = bar.get_width()
        if clipped:
            # Break marks
            gap_h = Y_CAP * 0.025
            ax.fill_between([bx, bx + bw], Y_CAP - gap_h, Y_CAP + gap_h,
                            color="white", zorder=5)
            slant = Y_CAP * 0.015
            for dy in [-gap_h * 0.5, gap_h * 0.5]:
                ax.plot([bx, bx + bw], [Y_CAP + dy - slant, Y_CAP + dy + slant],
                        color="#888888", linewidth=0.7, zorder=6)
            # Clipped label
            label_y = Y_CAP + effective_cap * 0.04
            ax.text(bx + bw / 2, label_y,
                    f"{val:.2f}", ha="center", va="bottom",
                    fontsize=label_fontsize, color="#222222", fontweight="bold",
                    rotation=90)
        else:
            pad = effective_cap * 0.015
            ax.text(bx + bw / 2, val + pad,
                    f"{val:.2f}", ha="center", va="bottom",
                    fontsize=label_fontsize, color="#222222",
                    rotation=90)

# Separator line between easy and hard sections
separator_x = len(both_easy) - 0.5
ax.axvline(separator_x, color="#CCCCCC", linewidth=0.8, linestyle="--", zorder=1)

ax.set_ylabel("Verification Time (s)", fontsize=11, labelpad=8)
ax.set_xticks(x)
ax.set_xticklabels(names, rotation=30, ha="right", fontsize=8.5)
ax.tick_params(axis="y", labelsize=9)

ax.yaxis.grid(True, linestyle="-", alpha=0.15, color="#000000", zorder=0)
ax.xaxis.grid(False)
ax.set_axisbelow(True)

ax.spines["top"].set_visible(False)
ax.spines["right"].set_visible(False)
ax.spines["left"].set_linewidth(0.6)
ax.spines["bottom"].set_linewidth(0.6)

if Y_CAP is not None:
    ax.set_ylim(0, Y_CAP * 1.1)
else:
    ax.set_ylim(0, y_max * 1.10)

ax.legend(loc="upper left", bbox_to_anchor=(0.01, 0.92), fontsize=9,
          frameon=True, facecolor="white", edgecolor="lightgray")

plt.tight_layout()

output_path = "/Users/volodeyka/conductor/workspaces/loom2/thebes/Loom/Test/Velvet/Bench/benchmark_comparison.pdf"
plt.savefig(output_path, bbox_inches="tight", facecolor="white")
plt.close(fig)

print(f"PDF saved to: {output_path}")
