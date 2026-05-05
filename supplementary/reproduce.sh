#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$DIR"

echo "=== Formal-AVS Reproduction Script ==="
echo "Regenerating headline tables from cached drafter outputs."
echo

# Step 1: Verify Lean library compiles
echo "[1/3] Verifying companion library (lake build)..."
if command -v lake &>/dev/null; then
    cd lean/
    lake exe cache get 2>&1 | tail -1
    lake build 2>&1 | tail -1
    echo "  Companion library: BUILD OK"
    cd "$DIR"
else
    echo "  SKIP: lake not found (install elan for full verification)"
fi

# Step 2: Regenerate headline tables
echo
echo "[2/3] Regenerating Table 1 (per-drafter closure rates)..."
python3 scripts/reproduce_headline.py \
    --slate data/slate_n5.json \
    --results results/ \
    --table headline

echo
echo "[3/3] Regenerating Table 2 (prompt sensitivity / capability ladder)..."
python3 scripts/reproduce_headline.py \
    --slate data/slate_n5.json \
    --results results/ \
    --table prompt_sensitivity

echo
echo "=== Done. All cells regenerated from cached outputs. ==="
