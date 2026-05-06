# Reproducing the Results

## Prerequisites

- Lean 4 (via [elan](https://github.com/leanprover/elan))
- Python 3.10+
- Docker (optional, for isolated verification)

## Quick Verification (cached outputs)

```bash
bash reproduce.sh
```

This regenerates all numeric cells in Tables 1-2 from cached drafter
outputs without re-running the models.

## Artifacts

| Artifact | Path | Description |
|---|---|---|
| Full benchmark | `data/benchmark.jsonl` | 60-target JSONL with tiers, statements, and per-drafter closure records |
| Aristotle history | `data/aristotle_history.jsonl` | 14-session Aristotle archive with verdicts, proofs, and axiom audits |
| Benchmark slate | `data/slate_n5.json` | 48-target evaluated slate (T0-T3) |
| Selection log | `data/selection_log.csv` | Per-target inclusion/exclusion record for the 48-slate |
| Companion library | `lean/` | formal-avs-lean source, Lean 4 v4.28.0 |
| Drafter outputs | `results/` | Per-cell JSON with proof candidates |
| Prompt templates | `scripts/prompts/` | Hint-list and neutral prompts |
| Reproduce script | `reproduce.sh` | One-command table regeneration |

## Lean Library Verification

```bash
cd lean/
lake exe cache get   # download Mathlib oleans (~20s)
lake build           # compile companion library (~60s)
```

The companion library provides the rate functions and dependency
lemmas that Mathlib does not yet supply. All dependency lemmas are
sorry-free; benchmark TARGET theorems contain sorry (these are what
solvers attempt to close).

## lib-snapshot

The companion library `formal-avs-lean` is pinned to:
- Lean: `leanprover/lean4:v4.28.0`
- Mathlib: commit listed in `lean/lake-manifest.json`

## Table Regeneration

`reproduce.sh` reads `results/*.json` and `results/*.csv`, computes
pass@N rates and Wilson CIs, and prints the headline tables. No
network access required.

## Dataset

The benchmark dataset is hosted on HuggingFace:
https://huggingface.co/datasets/neurips-2026-avs-bench/formal-anytime-valid-stats

60 targets with per-drafter closure rates, Lean statements, and tier classifications (T0-T5).
