# neurips-2026-dataset-paper

NeurIPS 2026 Datasets & Benchmarks Track submission:
**"Formal-AVS: a Lean benchmark for anytime-valid
confidence-sequence theorem proving"**

Benchmark of 60 Lean~4 theorems on anytime-valid confidence
sequences (CS) across four families (HR, betting, Whitehouse
vector, asymptotic CLT), released alongside a 14-session
Aristotle-prover history archive.

## Structure

- `main.tex` + `sections/` — paper source (NeurIPS 2026 format).
- `figures/heatmap.pdf` — per-target pass@5 heatmap across five
  drafters on the 48-target drafter-testable slate.
- `references.bib` — bibliography.
- `paper_lint.toml` — paper_lint config for this venue.
- `tools/check_paper.py` — local sanity check driver.

## Build

```bash
bash build.sh          # pdflatex x3 + bibtex
```

Requires TeX Live with `texlive-latex-extra`, `texlive-science`.

## Paper lint

```bash
cd /path/to/athanor-builder
python3 -m tools.paper_lint /path/to/neurips-2026-dataset-paper
```

## Companion artefacts

- **Benchmark JSONL + Aristotle history:** `neurips-2026-avs-bench/formal-anytime-valid-stats` on Hugging Face (CC-BY-4.0).
- **Lean library (formal-avs-lean):** Apache-2.0 Lean~4 library
  that instantiates the four CS families plus Ville's inequality
  and the quantization-transport lemma.
- **DSPv2-7B GPTQ-quantised weights:** Hugging Face model release.

## Tier structure

- T0 (7): Mathlib-canon lemmas.
- T1 (34): single-function friendly (positivity, monotonicity).
- T2 (8): single-function challenging (multi-step).
- T3 (6): cross-family inequalities (the capability wall).
- T4 (4): library-gap theorems (Mathlib API missing).
- T5 (1): capability-ceiling target (no solver closes).

## Headline results

- T0 drafter aggregate: 0/28 at N=5 across 4 generalist drafters.
- T3 drafter aggregate: 2/24 at N=5 across 4 generalist drafters.
- T3 Aristotle closure: 6/6 axiom-clean.
- 3 refutations: Aristotle returns counterexample witnesses on
  3 targets whose as-stated form is mathematically false.

## ATH tracking

- ATH-592 — paper polish pass (v1 draft ship state).
- ATH-508 — benchmark 60-theorem tier structure.
