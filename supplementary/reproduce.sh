#!/usr/bin/env bash
# Reproduce all headline numbers from the paper.
# Runtime: ~2 min (Lean optional, tables are instant from cached data).
# Requirements: Python 3.10+
#               Lean 4 via elan (https://github.com/leanprover/elan) — optional
set -euo pipefail
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$DIR"

echo "[1/2] Lean: verify companion library (optional — skipped if lake not found)"
if command -v lake &>/dev/null; then
    cd lean/
    lake exe cache get 2>&1 | tail -1
    lake build 2>&1 | tail -1
    echo "  Lean: BUILD OK"
    cd "$DIR"
else
    echo "  SKIP: lake not found (install elan for full Lean verification)"
fi

echo
echo "[2/2] Regenerating Table 1 from cached drafter outputs"
python3 scripts/reproduce_headline.py data/benchmark.jsonl

echo
echo "Done."
