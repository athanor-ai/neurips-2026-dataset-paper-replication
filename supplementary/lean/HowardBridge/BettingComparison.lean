/-
HowardBridge.BettingComparison — the T2 theorem for the Formal-AVS
benchmark paper "Deployable anytime-valid inference: machine-checked
implementations".

Axiom-audit target: {propext, Classical.choice, Quot.sound} only.
-/

import HowardBridge.Basic
import HowardBridge.SharpConstant
import Mathlib

namespace HowardBridge

open scoped Classical BigOperators

/-!
## Betting wealth process at finite precision
-/

/-- A betting-based martingale analogue: a non-negative wealth
process `W : Time → ℝ` with `W 0 = 1` and log-scale quantizable
increments bounded by the sub-Gaussian envelope of parameter `σ`. -/
structure BettingProcess (σ : ℝ) where
  wealth : Time → ℝ
  init : wealth 0 = 1
  pos : ∀ t : Time, 0 < wealth t
  logSubGaussian : ∀ (t : Time) (lam : ℝ),
    ∃ bound : ℝ, bound ≤ Real.exp (lam^2 * σ^2 / 2)
  sigma_pos : 0 < σ

/-- The betting-CS slack at bit-precision `bp` and sub-Gaussian
parameter `σ`. Rate: `2^{-s} · σ / √(b · log 2 + 1)`. -/
noncomputable def bettingSlack (σ : ℝ) (bp : BitPrecision) : ℝ :=
  (2 : ℝ)^(-(bp.scale : ℤ)) * σ /
    Real.sqrt ((bp.bits : ℝ) * Real.log 2 + 1)

/-- Non-negativity of the betting slack. -/
theorem bettingSlack_nonneg (σ : ℝ) (bp : BitPrecision) (hσ : 0 ≤ σ) :
    0 ≤ bettingSlack σ bp := by
  unfold bettingSlack
  exact div_nonneg (mul_nonneg (by positivity) hσ) (by positivity)

/-!
## Refutation infrastructure

`UpperValid c` is false for every `c : ℝ`. The always-stop implementation
with zero martingale satisfies `BitInvariants` at every `σ > 0`, and has
`realizedCoverage = 1 > α + sharpSlack c σ bp` when `σ` is small enough
(for `c > 0`) or when `c ≤ 0` (sharpSlack ≤ 0).
-/

/-
**No finite `c` is a valid upper constant.** For `c ≤ 0`:
`sharpSlack ≤ 0` so `1 > α`. For `c > 0`: pick
`σ = 1/(4c√(log 2))` so `sharpSlack = 1/4` and `1 > 3/4`.

**2026-04-22 Round-3 refutation retired.** Aristotle's round-3
refutation of `UpperValid` constructed an always-stop impl with zero
martingale. That construction no longer satisfies `BitInvariants`
because I5 (`quantized_decision_consistent`) requires
`decide t = true ↔ mart ≥ positive threshold`, but the always-stop
impl has `decide = true` while `mart = 0 < threshold` at any `t ≥ 1`.

Retaining the lemma statement for the refutation gallery, but the
proof now requires exhibiting an impl satisfying the STRONGER I5 —
which we expect to fail because I5 rules out degenerate stoppers.
Aristotle round 6 is the appropriate venue to confirm this.
-/
theorem not_UpperValid (c : ℝ) : ¬ UpperValid c := by
  unfold UpperValid;
  push_neg;
  use 1 / 4 / ( |c| + 1 );
  refine' ⟨ ⟨ 1, 0, 1, by norm_num, by norm_num ⟩, _, _, _ ⟩ <;> norm_num [ realizedCoverage ];
  refine' ⟨ _, fun _ _ => Bool.true, _ ⟩;
  refine' ⟨ fun _ => 0, _, _ ⟩ <;> norm_num;
  exact fun lam => ⟨ _, le_rfl ⟩;
  positivity;
  grind;
  · constructor <;> norm_num;
  · refine' ⟨ ⟨ 1 / 2, 0, _, _ ⟩, _ ⟩ <;> norm_num [ sharpSlack ];
    field_simp;
    cases abs_cases c <;> nlinarith [ Real.sqrt_nonneg ( Real.log 2 ), Real.sq_sqrt ( Real.log_nonneg one_le_two ), Real.log_le_sub_one_of_pos zero_lt_two ]

-- Aristotle round 6: either close (if a non-degenerate impl
         -- still defeats UpperValid 0) or refute (`UpperValid` is
         -- now PROVABLE for c ≥ c_HR_sharp — paper's Master Theorem
         -- recovered under I5).

/-- The valid upper constant set is empty. -/
theorem upperValidSet_empty : upperValidSet = ∅ := by
  ext c; simp [upperValidSet, not_UpperValid c]

/-- `c_HR = 0` since no valid upper constant exists. -/
theorem c_HR_eq_zero : c_HR = 0 := by
  unfold c_HR c_HR_upper; rw [upperValidSet_empty]; exact Real.sInf_empty

/-- `UpperValid c_HR` is false. -/
theorem not_UpperValid_c_HR : ¬ UpperValid c_HR := not_UpperValid c_HR

/-!
## T2 comparison theorem — vacuously true from false hypothesis
-/

/-
ORIGINAL STATEMENT (vacuously true — hypothesis `UpperValid c_HR`
is false, see `not_UpperValid_c_HR` above):

   The theorem is technically provable because the hypothesis
   `_h_c_HR_upper : UpperValid c_HR` is inconsistent.
   Any conclusion follows from False.

   Root cause: `UpperValid c` quantifies over ALL `σ > 0` and ALL
   `BitPrecision`, but the always-stop implementation with zero
   martingale satisfies `BitInvariants` at every `σ` and `bp`.
   For small enough `σ`, `sharpSlack c σ bp` becomes arbitrarily
   small, making `realizedCoverage = 1 > α + sharpSlack` inevitable.
   No finite `c` can compensate, so `upperValidSet = ∅` and
   `c_HR = sInf ∅ = 0`.
-/
theorem T2_betting_comparison
    (σ : ℝ) (bp : BitPrecision)
    (hσ : 0 < σ) (hb : 0 < bp.bits)
    (_h_bettingUpper : True)
    (_h_c_HR_upper : UpperValid c_HR) :
    ∀ (c_sharp : ℝ), c_sharp = c_HR →
      bettingSlack σ bp * Real.sqrt ((bp.bits : ℝ) * Real.log 2 + 1)
        ≤ sharpSlack c_sharp σ bp *
            Real.sqrt ((bp.bits : ℝ) * Real.log 2 + 1) := by
  exact absurd _h_c_HR_upper not_UpperValid_c_HR

/-
ORIGINAL STATEMENT (commented out — false as stated):

   `c_HR = 0` (since `upperValidSet = ∅`), so `sharpSlack c_HR σ bp = 0`.
   But `bettingSlack σ bp > 0` for `σ > 0`. The theorem claims
   `positive < 0`, which is false.

   Counterexample: σ = 1, bits = 1, scale = 0.
   `bettingSlack = 1/√(log2+1) ≈ 0.77 > 0 = sharpSlack 0`.

theorem T2_ratio_bound
    (σ : ℝ) (bp : BitPrecision)
    (hσ : 0 < σ) (hb : 1 ≤ bp.bits) :
    bettingSlack σ bp <
      sharpSlack c_HR σ bp := by
  sorry
-/

/-- **Refutation of `T2_ratio_bound`.** Since `c_HR = 0`,
`sharpSlack c_HR σ bp = 0`, while `bettingSlack σ bp > 0` for `σ > 0`.
Hence `bettingSlack < sharpSlack c_HR` is false. -/
theorem T2_ratio_bound_false :
    ∃ (σ : ℝ) (bp : BitPrecision),
      0 < σ ∧ 1 ≤ bp.bits ∧
      ¬ (bettingSlack σ bp < sharpSlack c_HR σ bp) := by
  refine ⟨1, ⟨1, 0, 0, by omega, by omega⟩, one_pos, le_refl 1, ?_⟩
  push_neg
  rw [c_HR_eq_zero]
  simp [sharpSlack]
  exact bettingSlack_nonneg 1 ⟨1, 0, 0, by omega, by omega⟩ (by norm_num)

end HowardBridge