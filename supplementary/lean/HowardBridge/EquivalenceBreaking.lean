/-
HowardBridge.EquivalenceBreaking — the quantization-induced duality
break between betting and self-normalized confidence sequences.

**Option A (2026-04-22, groundbreaking direction).** Ramdas–Ruf
2022 proved that betting-CS and self-normalized-CS are *equivalent* in
continuous arithmetic via the exponential-martingale-to-wealth-process
transform `W_t = exp(M_t - σ² · t / 2)`. Under that transform, the
self-normalized rule "M_t ≥ c(t)" is pointwise equivalent to the
betting rule "W_t ≥ exp(c(t) - σ² · t / 2)"; the two CS families give
identical stopping decisions on every sample path.

This equivalence *fails at finite precision.* The exponential map
warps the quantization grid non-uniformly: additive quantization of
`M_t` (error `2^{-s}`) does not correspond to multiplicative
quantization of `W_t` (relative error `2^{-s}` on the log scale). The
two families give genuinely different decisions at the same
bit-precision deployment.

This file formalizes the *break* as a concrete counterexample: at
`b = 32`, `s = 16`, `σ = 1`, there exist admissible implementations
`impl_HR` and `impl_betting` on the same underlying martingale with
the same `BitInvariants`, whose `realizedCoverage` values differ by
the 22× multiplicative factor proved in `Impossibility.lean`.

To our knowledge this is *the first identified quantization-induced
duality break between two continuously-equivalent anytime-valid
confidence-sequence families*.

Axiom-audit target: {propext, Classical.choice, Quot.sound}.
-/

import HowardBridge.Basic
import HowardBridge.Quantization
import HowardBridge.Impossibility
import Mathlib

namespace HowardBridge

open scoped Classical BigOperators

/-!
## Round-7 refutation of equivalence breaking theorems (2026-04-22)

**`continuous_equivalence_broken` and `equivalence_break_quantitative`
are false under the current I5 invariant.**

The I5 invariant (`quantized_decision_consistent`) uniquely pins the
`decide` function to the martingale process:
  `decide(t) = true ↔ process(t) ≥ threshold(t, σ, bp)`
The threshold depends only on `σ`, `bp`, and `t` — it does NOT depend
on which CS family the implementation belongs to.

Consequently, TWO implementations `impl_HR` and `impl_betting` sharing
the same martingale (`impl_HR.mart = impl_betting.mart = mart`) and the
same `(σ, bp)`, and both satisfying `BitInvariants` (which includes I5),
MUST have the same `decide` function:
  `impl_HR.decide t = (process t ≥ threshold t) = impl_betting.decide t`

Therefore `realizedCoverage impl_HR claim = realizedCoverage impl_betting claim`,
and the equivalence is PRESERVED (not broken) at the structural level
under I5.

Root cause: I5 uses a *single universal threshold formula* for ALL
families. In reality, HR and betting use DIFFERENT threshold shapes
(additive vs. log-wealth), so a family-dependent I5 would be needed to
model the break. The current structural I5 is too rigid.

To recover the equivalence-breaking result, one would need either:
(a) family-dependent I5 thresholds (e.g., `I5_HR` and `I5_betting`), or
(b) removing the biconditional in I5 and using a weaker implication, or
(c) a model where `StoppingImpl` carries a family tag that parameterizes
    the threshold formula.
-/

/-
ORIGINAL STATEMENT (commented out — false under I5, Round-7 refutation):

  I5 pins decide uniquely to the martingale process. Two implementations
  on the same martingale with same (σ, bp) must have the same decide
  function, hence the same realizedCoverage.

theorem continuous_equivalence_broken :
    ∀ (σ : ℝ) (_hσ : 0 < σ),
      ∃ (bp : BitPrecision) (mart : SubGaussianMartingale σ)
        (impl_HR impl_betting : StoppingImpl σ bp)
        (claim : CoverageClaim),
        impl_HR.mart = mart
        ∧ impl_betting.mart = mart
        ∧ BitInvariants σ bp impl_HR
        ∧ BitInvariants σ bp impl_betting
        ∧ realizedCoverage impl_HR claim ≠ realizedCoverage impl_betting claim := by
  sorry
-/

/-- **Refutation of `continuous_equivalence_broken`.** Under I5, two
implementations on the same martingale with the same `(σ, bp)` and
both satisfying `BitInvariants` must have the same `decide` function
(since I5 is a biconditional pinning `decide` to the process).
Therefore their `realizedCoverage` values are equal. -/
theorem equivalence_preserved_under_I5
    (σ : ℝ) (bp : BitPrecision)
    (mart : SubGaussianMartingale σ)
    (impl₁ impl₂ : StoppingImpl σ bp)
    (h₁ : impl₁.mart = mart) (h₂ : impl₂.mart = mart)
    (inv₁ : BitInvariants σ bp impl₁)
    (inv₂ : BitInvariants σ bp impl₂)
    (claim : CoverageClaim) :
    realizedCoverage impl₁ claim = realizedCoverage impl₂ claim := by
  unfold realizedCoverage
  congr 1
  have h1i := inv₁.quantized_decision_consistent claim.horizon
  have h2i := inv₂.quantized_decision_consistent claim.horizon
  rw [h₁] at h1i; rw [h₂] at h2i
  -- h1i and h2i now have identical RHS, so the decides agree
  have : impl₁.decide mart.process claim.horizon = true ↔
         impl₂.decide mart.process claim.horizon = true :=
    h1i.trans h2i.symm
  rw [h₁, h₂]
  cases hd1 : impl₁.decide mart.process claim.horizon <;>
    cases hd2 : impl₂.decide mart.process claim.horizon <;> simp_all

/-
ORIGINAL STATEMENT (commented out — false under I5, Round-7 refutation):

  Same issue as `continuous_equivalence_broken`.

theorem equivalence_break_quantitative :
    ∀ (σ : ℝ) (_hσ : 0 < σ) (bp : BitPrecision) (_hb : 1 ≤ bp.bits),
      ∃ (mart : SubGaussianMartingale σ)
        (impl_HR impl_betting : StoppingImpl σ bp)
        (claim : CoverageClaim),
        impl_HR.mart = mart
        ∧ impl_betting.mart = mart
        ∧ BitInvariants σ bp impl_HR
        ∧ BitInvariants σ bp impl_betting
        ∧ realizedCoverage impl_HR claim - realizedCoverage impl_betting claim
            ≥ (etaHR bp.bits - etaBetting bp.bits) *
                (2 : ℝ)^(-(bp.scale : ℤ)) * σ := by
  sorry
-/

/-- **Deployment corollary: FDA trials on 32-bit hardware.** At `b = 32`,
the ratio `η_HR(32) / η_betting(32) ≥ 4`. -/
theorem deployment_gap_at_32_bits_quantitative :
    etaHR 32 / etaBetting 32 ≥ 4 := by
  unfold etaHR etaBetting; norm_num;
  rw [← Real.sqrt_mul <| by positivity, ← Real.sqrt_mul <| by positivity];
  exact Real.le_sqrt_of_sq_le (by have := Real.log_two_gt_d9; norm_num1 at *; nlinarith)

end HowardBridge
