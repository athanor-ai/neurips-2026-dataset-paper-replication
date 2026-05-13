# HowardBridge — bridge theorem scaffold for the Formal-AVS benchmark

Branch: scaffold. Tracks the companion library.

## What this is

A Lean 4 scaffold for the bridge theorem stated in the Formal-AVS
benchmark paper *Deployable anytime-valid inference: machine-checked
implementations*:

> Let `impl` be a bit-precise implementation of a Howard-Ramdas
> stopping rule with bit-precision parameters `bp`. If `impl`
> satisfies bit-level invariants I1..I4, then the implementation's
> stopping probability by horizon `T` is bounded by `α + ε(σ, bp)`,
> where `ε` is the slack function defined in this file.

## Files

- `Basic.lean` — definitions (SubGaussianMartingale, BitPrecision,
  CoverageClaim, StoppingImpl, BitInvariants, slack) + main theorem
  `howard_bridge` + three helper lemmas (`slack_nonneg`,
  `slack_antitone_in_scale`, `slack_limit_zero`) +
  `howard_bridge_trivial_invariants` smoke test.

## State

Scaffold compiles (`lake env lean HowardBridge/Basic.lean` — no
errors, 4 sorry warnings + unused-variable warnings). Every theorem
has a sorried proof pending Aristotle + LLM closure.

## Next step (Phase 0)

SDK drives closure:

```bash
solve/core/run.sh --vertical sysverilog-fleet \
    --target howard_bridge_obf \
    --verifier lean,aristotle \
    --model openai/kimi-k2.5 \
    --max-iter 3
```

The SDK calls Aristotle first on every sorry, LLM fallback on
residuals, axiom audit gated at ship time.

## Budget

Scaffold: $0 (already done).
Aristotle first pass: $0 (free).
LLM residuals: capped at $15.

## Related

- Parent tracking ticket for the Formal-AVS benchmark paper.
- Paper-priority gating: this paper uses shared infrastructure,
  not the IP-gated research code.
