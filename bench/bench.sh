#!/usr/bin/env bash
set -e
cd "$(dirname "$0")/.."

case "${1:-run}" in
  run)       python3 bench/run.py "${@:2}" ;;
  plot)      python3 bench/run.py --plot-only "${@:2}" ;;
  baseline)  python3 bench/run.py --save-baseline ;;
  *)         echo "Usage: bench/bench.sh {run|plot|baseline} [args...]"
             echo ""
             echo "Commands:"
             echo "  run       Run all benchmarks and generate plots (default)"
             echo "  plot      Regenerate plots from existing data"
             echo "  baseline  Save current results as baseline"
             echo ""
             echo "Options (for 'run'):"
             echo "  --filter SUBSTR   Only run benchmarks matching substring"
             echo "  --sizes N,N,...   Override sizes (default: 100,200,...,1000)"
             echo "  --timeout SEC     Per-size timeout (default: 60)"
             ;;
esac
