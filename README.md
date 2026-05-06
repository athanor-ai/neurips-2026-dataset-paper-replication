# Replication package — Formal-AVS: A Lean Benchmark for Anytime-Valid CS Theorem Proving

NeurIPS 2026 Datasets & Benchmarks submission.

## One command

```bash
bash supplementary/reproduce.sh
```

Regenerates all headline table numbers from cached drafter outputs (~2 min).

## Requirements

- Python 3.10+
- Lean 4 via [elan](https://github.com/leanprover/elan) *(optional — skipped if not installed)*

## What gets reproduced

| Step | Output | Paper location |
|------|--------|----------------|
| Lean library build | `supplementary/lean/` builds clean | §2.2 |
| Table 1 (per-drafter closure rates) | printed to stdout | Table 1 |
| Table 2 (prompt sensitivity / capability ladder) | printed to stdout | Table 2 |

## Structure

```
supplementary/
  data/          benchmark.jsonl, aristotle_history.jsonl, slate_n5.json
  results/       cached drafter outputs (JSON/CSV)
  scripts/       reproduce_headline.py, prompt templates
  lean/          HowardBridge Lean 4 scaffold (benchmark targets)
  reproduce.sh   one-command reproducer
  REPRODUCE.md   detailed reproduction notes
```

## Dataset link

https://huggingface.co/datasets/neurips-2026-avs-bench/formal-anytime-valid-stats
