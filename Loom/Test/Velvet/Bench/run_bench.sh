#!/bin/bash
THEBES="/Users/volodeyka/conductor/workspaces/loom2/thebes"
BENCH_DIR="$THEBES/Loom/Test/Velvet/Bench"

echo "program,loom2_time,status"
for f in "$BENCH_DIR"/*.lean; do
  fname=$(basename "$f" .lean)
  [[ "$fname" == "All" || "$fname" == "MinReprSymSimp" || "$fname" == "Profile" || "$fname" == "ExpensiveGoals" || "$fname" == "run_bench" ]] && continue
  
  # Clean this specific olean to force fresh build
  rm -f "$THEBES/.lake/build/lib/lean/Loom/Test/Velvet/Bench/${fname}.olean" 2>/dev/null
  rm -f "$THEBES/.lake/build/lib/lean/Loom/Test/Velvet/Bench/${fname}.ilean" 2>/dev/null
  
  start=$(python3 -c "import time; print(time.perf_counter())")
  output=$(cd "$THEBES" && lake env lean "$f" 2>&1)
  end=$(python3 -c "import time; print(time.perf_counter())")
  elapsed=$(python3 -c "print($end - $start)")
  
  if echo "$output" | grep -q "^error"; then
    status="error"
  else
    status="ok"
  fi
  
  echo "$fname,$elapsed,$status"
done
