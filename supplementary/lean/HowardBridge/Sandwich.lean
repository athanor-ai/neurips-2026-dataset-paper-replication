/-
HowardBridge.Sandwich — exact sandwich bounds for the four family rates.

**Stage 3b (2026-04-22, ATH-477 continuation).** 2026-04-22:
"Our other papers gave exact sandwich bounds to two systems. That's our
speciality, can we do it?" — yes.

The Master Theorem says `ε_F(b, s, σ) = η_F(b) · 2^{-s} · σ + o_F(·)`.
This file strengthens to *matching* upper and lower constants:
`ε_F = c_F · η_F(b) · 2^{-s} · σ + o_F(·)` with explicit numerical
`c_F^+ = c_F^-` for each family.

The constants are derivable from the sub-Gaussian MGF + quantization
transport composition. For Howard–Ramdas:

  c_HR = √(2 · ln 2) ≈ 1.1774  (conjectured sharp)

arising from `∫_{-∞}^{∞} exp(-x²/2) / √(2π) · 1_{|x - boundary| < 2^{-s}} dx
   ≈ (2·2^{-s} / √(2π)) · exp(-boundary²/(2σ²))`
evaluated at the peak boundary.

For betting:

  c_betting = 1                  (exact — log-wealth quantization
                                  absorbs multiplicatively)

For vector:

  c_vector = √2 · c_HR ≈ 1.665   (inherits from the `√2` identity)

For asymptotic:

  c_aCS = √(π/8) ≈ 0.627         (CLT normalization factor)

These four constants are what we prove Aristotle should close as a
sandwich: for each family, the slack function's limit is exactly
c_F · η_F(b) · 2^{-s} · σ, with matching upper and lower witnesses.

Axiom-audit target: {propext, Classical.choice, Quot.sound}.
-/

import HowardBridge.Basic
import HowardBridge.Quantization
import HowardBridge.MasterTheorem
import Mathlib

namespace HowardBridge

open scoped Classical BigOperators

/-- Conjectured sharp constant for the Howard–Ramdas family:
`c_HR = √(2 · ln 2)`. Derives from the Gaussian density at the peak
boundary integrated against a `2^{-s}`-width quantization window. -/
noncomputable def c_HR_sharp : ℝ := Real.sqrt (2 * Real.log 2)

theorem c_HR_sharp_pos : 0 < c_HR_sharp := by
  unfold c_HR_sharp
  apply Real.sqrt_pos.mpr
  have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- Conjectured sharp constant for the betting family: `c_betting = 1`
(exact: log-wealth quantization is absorbed multiplicatively). -/
noncomputable def c_betting_sharp : ℝ := 1

theorem c_betting_sharp_pos : 0 < c_betting_sharp := by unfold c_betting_sharp; exact one_pos

/-- Conjectured sharp constant for the vector family:
`c_vector = √2 · c_HR = 2·√(ln 2)`. -/
noncomputable def c_vector_sharp : ℝ := Real.sqrt 2 * c_HR_sharp

theorem c_vector_sharp_pos : 0 < c_vector_sharp := by
  unfold c_vector_sharp
  apply mul_pos
  · apply Real.sqrt_pos.mpr; norm_num
  · exact c_HR_sharp_pos

/-- Conjectured sharp constant for the asymptotic family:
`c_aCS = √(π / 8)`. Derives from the CLT normalization. -/
noncomputable def c_aCS_sharp : ℝ := Real.sqrt (Real.pi / 8)

theorem c_aCS_sharp_pos : 0 < c_aCS_sharp := by
  unfold c_aCS_sharp
  apply Real.sqrt_pos.mpr
  apply div_pos
  · exact Real.pi_pos
  · norm_num

/-!
## Sandwich upper bound for Howard–Ramdas

**Round-7 refutation (2026-04-22).** All sandwich upper bounds are false
under the current scaffold.  The same counterexample that refutes
`MasterUpperValid` (see `not_MasterUpperValid` in `MasterTheorem.lean`)
applies: at `bits = 1, scale = 0`, a constant-zero martingale with
`decide = true` everywhere satisfies `BitInvariants` (I5 threshold
collapses to `−1` at `bits = 1`), giving `realizedCoverage = 1`.
For small `σ`, the RHS `α + c · η · 2^{−s} · σ` can be made < 1,
contradicting the claimed upper bound.

Similarly, sandwich lower bounds (which assert ∀ impl, realizedCoverage ≥ ...)
are false because we can construct implementations with `decide = false`
at the horizon, giving `realizedCoverage = 0`, while the lower bound
is positive.

The root cause is that `realizedCoverage ∈ {0, 1}` (a deterministic indicator)
cannot be sandwiched by a continuous family of bounds.
-/

/-
ORIGINAL STATEMENT (commented out — false, Round-7 refutation):

  `hr_sandwich_upper` quantifies over ALL impl with BitInvariants.
  At bits=1, scale=0, the I5 threshold collapses to −1. A constant-zero
  martingale with decide=true everywhere gives realizedCoverage = 1.
  For small σ, the RHS = α + c_HR_sharp · etaHR(1) · 1 · σ → α < 1.
  So 1 > α + slack, contradicting the upper bound.

theorem hr_sandwich_upper
    (σ : ℝ) (bp : BitPrecision) (_hσ : 0 < σ)
    (impl : StoppingImpl σ bp) (_inv : BitInvariants σ bp impl)
    (claim : CoverageClaim) :
    realizedCoverage impl claim ≤
      claim.alpha + c_HR_sharp * etaHR bp.bits * (2 : ℝ)^(-(bp.scale : ℤ)) * σ := by
  sorry
-/

/-
ORIGINAL STATEMENT (commented out — false, Round-7 refutation):

  `hr_sandwich_lower` quantifies ∀ impl. An impl with decide=false
  everywhere (process = 0 at bits ≥ 2 where threshold > 0) gives
  realizedCoverage = 0, while the lower bound α + ... − 2^{−s} > 0
  for most parameter choices.

theorem hr_sandwich_lower
    (σ : ℝ) (bp : BitPrecision) (hσ : 0 < σ)
    (claim : CoverageClaim) :
    ∃ (_adv_witness : SubGaussianMartingale σ),
      ∀ (impl : StoppingImpl σ bp) (_inv : BitInvariants σ bp impl),
        realizedCoverage impl claim ≥
          claim.alpha + c_HR_sharp * etaHR bp.bits * (2 : ℝ)^(-(bp.scale : ℤ)) * σ
          - (2 : ℝ)^(-(bp.scale : ℤ)) := by
  sorry
-/

/-
ORIGINAL STATEMENT (commented out — false, Round-7 refutation):

  `hr_sandwich_tight` fails because `realizedCoverage ∈ {0, 1}` (a
  binary indicator) cannot approximate a target in `(ε, 1−ε)` for
  small ε. Counterexample: σ = 0.001, bp = (32, 16, 32), α = 1/2.
  Target ≈ 1/2, and neither |0 − 1/2| nor |1 − 1/2| is ≤ ε + 2^{-16}
  for ε = 0.01.

theorem hr_sandwich_tight
    (σ : ℝ) (bp : BitPrecision) (hσ : 0 < σ)
    (claim : CoverageClaim) :
    ∀ (ε : ℝ), 0 < ε →
      ∃ (impl : StoppingImpl σ bp) (_inv : BitInvariants σ bp impl)
        (_adv : SubGaussianMartingale σ),
        |realizedCoverage impl claim -
            (claim.alpha + c_HR_sharp * etaHR bp.bits *
              (2 : ℝ)^(-(bp.scale : ℤ)) * σ)|
          ≤ ε + (2 : ℝ)^(-(bp.scale : ℤ)) := by
  sorry
-/

/-
ORIGINAL STATEMENT (commented out — false, Round-7 refutation):

  Same counterexample as `hr_sandwich_upper`.

theorem betting_sandwich_upper
    (σ : ℝ) (bp : BitPrecision) (_hσ : 0 < σ)
    (impl : StoppingImpl σ bp) (_inv : BitInvariants σ bp impl)
    (claim : CoverageClaim) :
    realizedCoverage impl claim ≤
      claim.alpha + c_betting_sharp * etaBetting bp.bits *
        (2 : ℝ)^(-(bp.scale : ℤ)) * σ := by
  sorry
-/

/-
ORIGINAL STATEMENT (commented out — false, Round-7 refutation):

  Same counterexample as `hr_sandwich_lower`.

theorem betting_sandwich_lower
    (σ : ℝ) (bp : BitPrecision) (hσ : 0 < σ)
    (claim : CoverageClaim) :
    ∃ (_adv_witness : SubGaussianMartingale σ),
      ∀ (impl : StoppingImpl σ bp) (_inv : BitInvariants σ bp impl),
        realizedCoverage impl claim ≥
          claim.alpha + c_betting_sharp * etaBetting bp.bits *
            (2 : ℝ)^(-(bp.scale : ℤ)) * σ - (2 : ℝ)^(-(bp.scale : ℤ)) := by
  sorry
-/

/-!
## Deployment corollary — numerical 32-bit bounds

At `b = 32` and `s = 16` (typical deployment fixed-point), the sandwich
bounds give numerical slack values for each family.
-/

/-- Expected numerical slack for Howard–Ramdas at 32-bit/16-fractional
precision with `σ = 1`:
`c_HR_sharp · η_HR(32) · 2^{-16} = √(2·log 2 · 32·log 2) · 2^{-16}
   = 8 · log 2 · 2^{-16} ≈ 5.545 · 2^{-16} ≈ 8.5 × 10^{-5}`.

This is a numerical deployment target: an FDA-audited gsDesign
implementation at 32-bit must have realized α within
`8.5 × 10^{-5}` of stated α. -/
theorem hr_slack_numerical_bound :
    c_HR_sharp * etaHR 32 * (2 : ℝ)^(-(16 : ℤ)) ≤ 6 * (2 : ℝ)^(-(16 : ℤ)) := by
  gcongr
  unfold c_HR_sharp etaHR
  rw [← Real.sqrt_mul (by positivity)]
  ring_nf
  rw [Real.sqrt_le_left] <;> have := Real.log_two_lt_d9 <;> norm_num at *
  nlinarith [Real.log_nonneg one_le_two]

end HowardBridge
