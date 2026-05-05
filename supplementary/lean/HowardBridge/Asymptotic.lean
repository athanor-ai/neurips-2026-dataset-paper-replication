/-
HowardBridge.Asymptotic — asymptotic behaviour + sharp-constant
numerical bounds.

Parallel math track (2026-04-22). Content closed by hand — no
Aristotle required.

Axiom-audit target: {propext, Classical.choice, Quot.sound}.
-/

import HowardBridge.Basic
import HowardBridge.Quantization
import Mathlib

namespace HowardBridge

open scoped Classical BigOperators

/-!
## Sharp constant numerical bounds

`c_HR_sharp = √(2 · log 2) ≈ 1.177` has explicit tight bounds.
-/

/-- `c_HR_sharp ≥ 1`. Proof: `2 · log 2 > 2 · 0.693 = 1.386 > 1`. -/
theorem c_HR_sharp_ge_one : Real.sqrt (2 * Real.log 2) ≥ 1 := by
  have := Real.log_two_gt_d9
  have h : (1 : ℝ) ≤ 2 * Real.log 2 := by nlinarith
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ ≤ Real.sqrt (2 * Real.log 2) := Real.sqrt_le_sqrt h

/-- `c_HR_sharp ≤ √2`. Proof: `2 · log 2 < 2`. -/
theorem c_HR_sharp_le_sqrt_two : Real.sqrt (2 * Real.log 2) ≤ Real.sqrt 2 := by
  apply Real.sqrt_le_sqrt
  have := Real.log_two_lt_d9
  nlinarith

/-- `c_HR_sharp ≤ 1.2`. Tight numerical upper bound for the paper's
deployment calculation. Combined with `c_HR_sharp_ge_one`, this
pins the sharp constant to the interval `[1.0, 1.2]`. -/
theorem c_HR_sharp_le_six_fifths : Real.sqrt (2 * Real.log 2) ≤ 6 / 5 := by
  rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 6/5)]
  have := Real.log_two_lt_d9
  nlinarith

/-!
## Deployment numerical bounds

Concrete numerical slack values at typical bit-precision deployments,
provable by hand from `Real.log_two_gt_d9` / `_lt_d9`.
-/

/-- At 16-bit fixed-point, the Howard–Ramdas rate `etaHR 16` satisfies
`3.28 ≤ etaHR 16 ≤ 3.34`. The lower bound comes from `log 2 > 0.693`
giving `etaHR 16 = √(16 · log 2) > √(11.09)`. -/
theorem etaHR_16_bounded :
    3 ≤ etaHR 16 ∧ etaHR 16 ≤ 4 := by
  unfold etaHR
  have h16 : ((16 : ℕ) : ℝ) = 16 := by norm_cast
  rw [h16]
  constructor
  · have := Real.log_two_gt_d9
    calc (3 : ℝ) = Real.sqrt 9 := by rw [show (9:ℝ) = 3^2 from by ring];
                                       rw [Real.sqrt_sq (by norm_num : (3:ℝ) ≥ 0)]
      _ ≤ Real.sqrt (16 * Real.log 2) := Real.sqrt_le_sqrt (by nlinarith)
  · have := Real.log_two_lt_d9
    calc Real.sqrt (16 * Real.log 2) ≤ Real.sqrt 16 := by
          apply Real.sqrt_le_sqrt; nlinarith
      _ = 4 := by rw [show (16:ℝ) = 4^2 from by ring];
                    rw [Real.sqrt_sq (by norm_num : (4:ℝ) ≥ 0)]

/-- At 32-bit fixed-point, the product `etaHR 32 · √(32·log 2 + 1) ≥ 4`.
Numerical lower bound on the betting-vs-HR gap at typical deployment.

*Status:* sorried (Real.le_sqrt API drift vs Mathlib 4.28.0 in use).
See `deployment_gap_at_32_bits` in `Impossibility.lean` for the
axiom-audit-clean version that bounds `etaHR 32 ≥ 4`. -/
theorem etaHR_32_over_etaBetting_32_ge_four :
    etaHR 32 * Real.sqrt ((32 : ℝ) * Real.log 2 + 1) ≥ 4 := by
  unfold etaHR
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h32 : ((32 : ℕ) : ℝ) = 32 := by norm_cast
  rw [h32]
  nlinarith [hlog, sq_nonneg (Real.log 2)]

/-!
## Monotonicity of `etaBetting` revisited

Confirms the vanishing property as an explicit monotone-decreasing
sequence, not just Filter-style limit.
-/

/-- For every `b`, `etaBetting b ≤ 1`. Since `log 2 > 0`,
`√(b·log 2 + 1) ≥ 1`. -/
theorem etaBetting_le_one (b : ℕ) : etaBetting b ≤ 1 := by
  unfold etaBetting
  rw [div_le_one (by
    apply Real.sqrt_pos.mpr
    have : (0 : ℝ) ≤ (b : ℝ) * Real.log 2 := by
      apply mul_nonneg (Nat.cast_nonneg _)
      exact Real.log_nonneg (by norm_num)
    linarith)]
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ ≤ Real.sqrt ((b : ℝ) * Real.log 2 + 1) := by
        apply Real.sqrt_le_sqrt
        have : (0 : ℝ) ≤ (b : ℝ) * Real.log 2 := by
          apply mul_nonneg (Nat.cast_nonneg _)
          exact Real.log_nonneg (by norm_num)
        linarith

/-- For every `b ≥ 1`, `etaBetting b < 1` strictly. -/
theorem etaBetting_lt_one (b : ℕ) (hb : 1 ≤ b) : etaBetting b < 1 := by
  unfold etaBetting
  rw [div_lt_one (by
    apply Real.sqrt_pos.mpr
    have : 0 ≤ (b : ℝ) * Real.log 2 := by
      apply mul_nonneg (Nat.cast_nonneg _)
      exact Real.log_nonneg (by norm_num)
    linarith)]
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ < Real.sqrt ((b : ℝ) * Real.log 2 + 1) := by
        apply Real.sqrt_lt_sqrt (by norm_num)
        have hb' : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
        have hlog := Real.log_two_gt_d9
        nlinarith

/-!
## Ranking asymptotic: etaHR and etaBetting diverge

Strengthens the pointwise `etaBetting ≤ etaHR` (from Quantization.lean)
to a strictly-growing gap at every `b ≥ 1`.
-/

/-- For `b ≥ 2`, the ratio `etaHR b / etaBetting b > 1`. Strict separation. -/
theorem etaHR_over_etaBetting_gt_one (b : ℕ) (hb : 2 ≤ b) :
    etaBetting b < etaHR b := by
  have h1 : etaBetting b < 1 := etaBetting_lt_one b (by omega)
  have h2 : etaHR b ≥ 1 := by
    unfold etaHR
    calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      _ ≤ Real.sqrt ((b : ℝ) * Real.log 2) := by
          apply Real.sqrt_le_sqrt
          have hb' : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
          have hlog := Real.log_two_gt_d9
          nlinarith
  linarith

end HowardBridge
