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

## Next step

Closure pipeline: a prover (Aristotle) attempts every `sorry` first,
an LLM drafter fills residuals where the prover does not converge,
and the axiom audit gates anything that ships. The driver is generic
over the choice of prover and drafter.

## Related

The bridge scaffold uses shared verification infrastructure rather
than any single proprietary code path. The released artifact in this
repository is intentionally a self-contained snapshot: it builds with
`lake exe cache get && lake build` against the pinned Mathlib commit
in `lakefile.lean`.
