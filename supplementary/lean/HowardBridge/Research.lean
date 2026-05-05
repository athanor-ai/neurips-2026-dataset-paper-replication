/-
HowardBridge.Research — Dichotomy Theorem + MasterSharpSlackAvgUniv
sub-theorem decomposition under the corrected canonical-trajectory
monotonicity scaffold (round-11→round-12 revision, 2026-04-23).

## Round-11 finding (promoted to Dichotomy Theorem)

Aristotle round 11 exhibited a structural refutation: the obvious
universal-monotonicity formulation of `StoppingImpl` (monotonicity
quantified over all trajectories) is **jointly unsatisfiable** with
universal I5 (threshold-check biconditional quantified over all
trajectories) for any strictly-increasing threshold.

The category error: deployment monotonicity (once-fired stickiness on
the observed sample path) is a PATH-SPECIFIC property. Lifting it to
a trajectory-universal property makes it contradict the mathematical
growth of the Howard-Ramdas threshold. Prior anytime-valid CS
specification work ambiguates between the two readings; our scaffold
caught the error.

`StoppingImpl.monotone` has been corrected to canonical-trajectory
scope (`Basic.lean`). This file states the Dichotomy Theorem as the
reason for the correction, and re-states the three sub-theorems of
`MasterSharpSlackAvgUniv` as genuine (non-vacuous) targets under the
corrected scaffold.

## Round-12 findings

### Sub-theorem (iii) — lower bound: CLOSED.
Constructive witness at `bits=1, scale=0` where the threshold
collapses to `−1`. All trajectories clear this degenerate threshold,
giving `realizedCoverageAvg = 1 ≥ α + F.slackFn` for σ small enough.

### Sub-theorem (ii) — upper bound: REFUTED.
The `SubGaussianMartingale` formalization has a vacuous `subGaussian`
field: `∃ bound, bound ≤ exp(λ²σ²/2)` is trivially satisfiable by
choosing `bound = exp(λ²σ²/2)` itself, regardless of the process.
Consequently, `AdversaryFamily` imposes no probabilistic constraint
on trajectories — an adversary can place all trajectories above any
threshold. The same `bits=1, scale=0` construction that closes (iii)
serves as a counterexample to (ii): `realizedCoverageAvg = 1` but
`α + F.slackFn < 1` for small σ.

Root cause: a genuine upper bound requires either (a) a proper
probability-space formalization of sub-Gaussianity with Mathlib's
`MeasureTheory`, or (b) a structural constraint on `AdversaryFamily`
preventing the adversary from placing all mass above the threshold.
The current deterministic scaffold cannot express step (2) of the
proof sketch ("fraction of trajectories exceeding τ is bounded by
exp(−τ²/(2σ²))") because that is a probabilistic statement about
measure, not a deterministic property of trajectory values.

### MasterSharpSlackAvgUniv: HALF-CLOSED.
The lower clause (`MasterLowerValidAvgUniv`) closes via (iii).
The upper clause (`MasterUpperValidAvgUniv`) is false under the
current formalization, as shown by the refutation theorem
`not_MasterUpperValidAvgUniv`. The conjunction
`MasterSharpSlackAvgUniv` is therefore false as stated.

## Axiom-audit target

`{propext, Classical.choice, Quot.sound}` only.
-/

import HowardBridge.Basic
import HowardBridge.Adversarial
import HowardBridge.SharpConstant
import HowardBridge.MasterTheorem
import Mathlib

namespace HowardBridge

open scoped Classical BigOperators

/-!
## Dichotomy Theorem

No decision function can satisfy both universal (trajectory-agnostic)
monotonicity and universal threshold-check for a strictly-increasing
threshold. This is the central finding of the round-11 refutation,
promoted to a paper-headline theorem about the anytime-valid CS
specification surface.

The theorem states a **negative existence** result: there is no function
`d : (Time → ℝ) → Time → Bool` jointly satisfying the two universal
properties. Consequence: deployment monotonicity must be specified
on the canonical trajectory only — it is path-specific, not
mathematical. -/

/-- **Dichotomy Theorem.** For any strictly-positive sub-Gaussian
parameter `σ` and any bit-precision `bp`, there is no decision
function that is simultaneously:

- **universally monotone**: `∀ x t, d x t = true → d x (t+1) = true`,
- **universally threshold-gated** at the Howard-Ramdas quantized
  threshold: `∀ x t, d x t = true ↔ x t ≥ threshold_hr σ bp t`.

Proof sketch: pick `x` with `x 0 = threshold_hr σ bp 0` and
`x 1 = threshold_hr σ bp 1 - 1`. Threshold-gating gives `d x 0 = true`
(since `x 0 ≥ threshold(0)`). Universal monotonicity gives `d x 1 =
true`. Threshold-gating reversed gives `x 1 ≥ threshold(1)`, but
`x 1 = threshold(1) - 1`. Contradiction.

Consequence: `StoppingImpl.monotone` must be path-specific
(canonical trajectory), as it now is in `Basic.lean`. -/
theorem dichotomy_universal_monotonicity_impossible
    (σ : ℝ) (hσ : 0 < σ) (bp : BitPrecision) :
    ¬ ∃ (d : (Time → ℝ) → Time → Bool),
        (∀ (x : Time → ℝ) (t : Time),
           d x t = true → d x (t + 1) = true)
        ∧ (∀ (x : Time → ℝ) (t : Time),
           d x t = true ↔
             x t ≥
               min (σ * Real.sqrt (((t : ℝ) + 1) * Real.log 2))
                   ((2 : ℝ)^(bp.bits - 1 : ℕ) - 1)
                 - (2 : ℝ)^(-(bp.scale : ℤ))) := by
  rintro ⟨d, mono, consistent⟩
  -- Threshold values at t=0 and t=1.
  let τ0 := min (σ * Real.sqrt (((0 : ℕ) + 1 : ℝ) * Real.log 2))
                ((2 : ℝ)^(bp.bits - 1 : ℕ) - 1)
              - (2 : ℝ)^(-(bp.scale : ℤ))
  let τ1 := min (σ * Real.sqrt (((1 : ℕ) + 1 : ℝ) * Real.log 2))
                ((2 : ℝ)^(bp.bits - 1 : ℕ) - 1)
              - (2 : ℝ)^(-(bp.scale : ℤ))
  -- Trajectory with x(0) = τ0, x(1) = τ1 - 1.
  let x : Time → ℝ := fun t => if t = 0 then τ0 else τ1 - 1
  -- Threshold-gating fires decide at t=0.
  have h0 : d x 0 = true := by
    rw [consistent x 0]
    simp [x, τ0]
  -- Universal monotonicity propagates to t=1.
  have h1 : d x 1 = true := mono x 0 h0
  -- Threshold-gating reversed: x(1) must clear τ1.
  have h1' : x 1 ≥ τ1 := (consistent x 1).mp h1
  -- But x(1) = τ1 - 1, contradiction.
  have hx1 : x 1 = τ1 - 1 := by simp [x]
  linarith

/-!
## Sub-theorem (i) — pointwise consequence of universal I5

Under the corrected scaffold (`StoppingImpl.monotone` canonical-only),
`BitInvariantsUniv` is satisfiable. Pointwise consequence of I5 is a
genuine (non-vacuous) result: if decide signals stop on any input
trajectory, the trajectory clears the threshold at that time.

Foundation for sub-theorem (ii).
-/
theorem decide_implies_threshold_cross
    (σ : ℝ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) (inv : BitInvariantsUniv σ bp impl)
    (x : Time → ℝ) (t : Time)
    (h : impl.decide x t = true) :
    x t ≥
      min (σ * Real.sqrt (((t : ℝ) + 1) * Real.log 2))
          ((2 : ℝ)^(bp.bits - 1 : ℕ) - 1)
        - (2 : ℝ)^(-(bp.scale : ℤ)) :=
  (inv.quantized_decision_consistent_univ x t).mp h

/-!
## Sub-theorem (ii) — averaged upper via sub-Gaussian MGF

**STATUS: REFUTED (Round 12).**

The theorem as stated is false. The proof sketch assumed that the
sub-Gaussian MGF bound constrains trajectory values probabilistically,
but the formalization's `SubGaussianMartingale.subGaussian` field is
vacuous: `∃ bound, bound ≤ exp(λ²σ²/2)` is trivially satisfiable
regardless of the process (choose `bound = exp(λ²σ²/2)`). Therefore,
`AdversaryFamily` imposes no constraint on trajectories, and an
adversary can place all trajectories above any threshold.

A genuine probabilistic upper bound would require either:
(a) A measure-theoretic `SubGaussianMartingale` with Mathlib's
    `MeasureTheory.Filtration` and genuine MGF bounds, or
(b) A structural constraint on `AdversaryFamily` limiting the fraction
    of trajectories that can exceed the threshold.

See `not_averaged_upper_from_mgf` for the formal refutation.
-/

/- ORIGINAL STATEMENT (commented out — false, see refutation below):

theorem averaged_upper_from_mgf
    (F : AdmissibleFamily)
    (σ : ℝ) (hσ : 0 < σ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) (inv : BitInvariantsUniv σ bp impl)
    (adv : AdversaryFamily σ) (claim : CoverageClaim) :
    realizedCoverageAvg impl adv claim ≤ claim.alpha + F.slackFn σ bp := by
  sorry

Root cause: the `SubGaussianMartingale.subGaussian` field is vacuously
satisfiable (see explanation above), so `AdversaryFamily` carries no
real probabilistic constraint. An adversary can construct a family where
ALL trajectories exceed the threshold, giving `realizedCoverageAvg = 1`,
while `α + F.slackFn < 1` for small σ.
-/

/-!
### Refutation of `averaged_upper_from_mgf`

The `bits=1, scale=0` construction collapses the threshold to `−1`.
Any trajectory with `process(t) ≥ −1` (e.g., the constant-zero
martingale) satisfies the threshold check, so all `decide` calls
return `true`, giving `realizedCoverageAvg = 1`. For small `σ`,
`α + F.slackFn < 1`, so `1 > α + F.slackFn`, contradicting the
upper bound.
-/

noncomputable section

/-- Bit-precision with `bits = 1, scale = 0`: threshold degenerates
to `−1` for any σ > 0. -/
private def bp10 : BitPrecision := ⟨1, 0, 1, one_pos, Nat.zero_le _⟩

/-- At `bits = 1, scale = 0`, the quantized threshold equals `−1`
for any σ > 0 and any time step t. -/
private lemma threshold_eq_neg1 (σ : ℝ) (hσ : 0 < σ) (t : ℕ) :
    min (σ * Real.sqrt (((t : ℝ) + 1) * Real.log 2))
        ((2 : ℝ)^(bp10.bits - 1 : ℕ) - 1)
      - (2 : ℝ)^(-(bp10.scale : ℤ)) = -1 := by
  simp only [bp10, Nat.sub_self, pow_zero, sub_self, zpow_neg, zpow_natCast, pow_zero, inv_one]
  have h : (0 : ℝ) ≤ σ * Real.sqrt (((t : ℝ) + 1) * Real.log 2) := by positivity
  rw [min_eq_right h]; ring

/-- Constant-zero sub-Gaussian martingale (vacuously satisfies the
MGF bound). -/
private def mkMart (σ : ℝ) (hσ : 0 < σ) : SubGaussianMartingale σ where
  process := fun _ => 0
  subGaussian := fun _ lam => ⟨Real.exp (lam ^ 2 * σ ^ 2 / 2), le_refl _⟩
  sigma_pos := hσ

/-- Threshold-check decision function: `true` iff `x t ≥ −1`. At
`bits = 1, scale = 0` this is equivalent to the quantized threshold
check. -/
private def mkDecide : (Time → ℝ) → Time → Bool :=
  fun x t => if x t ≥ (-1 : ℝ) then true else false

private lemma mkDecide_iff (x : Time → ℝ) (t : Time) :
    mkDecide x t = true ↔ x t ≥ -1 := by
  unfold mkDecide; split_ifs with h
  · exact iff_of_true rfl h
  · push_neg at h; exact iff_of_false (by simp) (by linarith)

/-- Stopping implementation with constant-zero martingale and
threshold-check decide at `bits = 1, scale = 0`. -/
private def mkImpl (σ : ℝ) (hσ : 0 < σ) : StoppingImpl σ bp10 where
  mart := mkMart σ hσ
  decide := mkDecide
  monotone := by intro t ht; rw [mkDecide_iff] at ht ⊢; simp [mkMart]

/-- The `mkImpl` construction satisfies `BitInvariantsUniv`:
- no-overflow: `|0| ≤ 1`
- bounded-accumulator: `|0| ≤ 2`
- I5' universal: `mkDecide x t = true ↔ x t ≥ threshold = −1`
-/
private def mkInv (σ : ℝ) (hσ : 0 < σ) :
    BitInvariantsUniv σ bp10 (mkImpl σ hσ) where
  no_overflow := by intro t; simp [mkImpl, mkMart, bp10]
  bounded_accumulator := by intro t; simp [mkImpl, mkMart, bp10]
  quantized_decision_consistent_univ := by
    intro x t; show mkDecide x t = true ↔ _
    rw [mkDecide_iff, threshold_eq_neg1 σ hσ t]

/-- Single-trajectory adversary: constant-zero process. -/
private def mkAdv (σ : ℝ) (hσ : 0 < σ) : AdversaryFamily σ where
  size := 1
  size_pos := one_pos
  trajectories := fun _ => mkMart σ hσ

/-- With constant-zero trajectories and threshold `−1`, every
trajectory fires decide at every time, giving
`realizedCoverageAvg = 1`. -/
private lemma coverage_is_one (σ : ℝ) (hσ : 0 < σ) (claim : CoverageClaim) :
    realizedCoverageAvg (mkImpl σ hσ) (mkAdv σ hσ) claim = 1 := by
  unfold realizedCoverageAvg; simp [mkImpl, mkAdv, mkDecide, mkMart]

end

/-- **Refutation of `averaged_upper_from_mgf`.** There exist `F, σ, bp,
impl, inv, adv, claim` such that `realizedCoverageAvg > α + F.slackFn`,
contradicting the proposed universal upper bound.

The construction uses `bits = 1, scale = 0` where the threshold
degenerates to `−1`. The constant-zero adversary gives
`realizedCoverageAvg = 1`, while `α + F.slackFn < 1` for small σ. -/
theorem not_averaged_upper_from_mgf :
    ∃ (F : AdmissibleFamily) (σ : ℝ) (_ : 0 < σ) (bp : BitPrecision)
      (impl : StoppingImpl σ bp) (_ : BitInvariantsUniv σ bp impl)
      (adv : AdversaryFamily σ) (claim : CoverageClaim),
      realizedCoverageAvg impl adv claim > claim.alpha + F.slackFn σ bp := by
  have heta : 0 ≤ familyHR.eta 1 := familyHR.eta_nonneg 1
  set σ := 1 / (4 * (familyHR.eta 1 + 1)) with hσ_def
  have hσ : 0 < σ := by rw [hσ_def]; positivity
  refine ⟨familyHR, σ, hσ, bp10, mkImpl σ hσ, mkInv σ hσ, mkAdv σ hσ,
    ⟨1/2, 0, by norm_num, by norm_num⟩, ?_⟩
  rw [coverage_is_one]
  unfold AdmissibleFamily.slackFn
  simp only [bp10, zpow_neg, zpow_natCast, pow_zero, inv_one]
  rw [hσ_def]
  have key : familyHR.eta 1 * (1 / (4 * (familyHR.eta 1 + 1))) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
    nlinarith
  linarith

/-- **Refutation of `MasterUpperValidAvgUniv`.** The universal upper
bound is false under the current formalization because the sub-Gaussian
MGF constraint is vacuous. Same construction as `not_averaged_upper_from_mgf`. -/
theorem not_MasterUpperValidAvgUniv (F : AdmissibleFamily) :
    ¬ MasterUpperValidAvgUniv F := by
  unfold MasterUpperValidAvgUniv; push_neg
  have heta : 0 ≤ F.eta 1 := F.eta_nonneg 1
  set σ := 1 / (4 * (F.eta 1 + 1)) with hσ_def
  have hσ : 0 < σ := by rw [hσ_def]; positivity
  refine ⟨σ, hσ, bp10, mkImpl σ hσ, mkInv σ hσ, mkAdv σ hσ,
    ⟨1/2, 0, by norm_num, by norm_num⟩, ?_⟩
  rw [coverage_is_one]
  unfold AdmissibleFamily.slackFn
  simp only [bp10, zpow_neg, zpow_natCast, pow_zero, inv_one]
  rw [hσ_def]
  have key : F.eta 1 * (1 / (4 * (F.eta 1 + 1))) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
    nlinarith
  linarith

/-!
## Sub-theorem (iii) — lower bound via threshold-degeneration

**STATUS: CLOSED (Round 12).**

Constructive witness: at `bits = 1, scale = 0`, the quantized threshold
degenerates to `−1`. A constant-zero martingale with threshold-check
decide satisfies `BitInvariantsUniv`. A single-trajectory adversary
(also constant-zero) gives `realizedCoverageAvg = 1 ≥ α + F.slackFn`
for σ small enough that `F.slackFn σ bp < 1 − α`.

This closes the lower clause of `MasterSharpSlackAvgUniv`.
-/
theorem lower_pigeonhole_adversary (F : AdmissibleFamily) :
    ∃ (σ : ℝ) (_hσ : 0 < σ) (bp : BitPrecision)
      (impl : StoppingImpl σ bp) (_inv : BitInvariantsUniv σ bp impl)
      (adv : AdversaryFamily σ) (claim : CoverageClaim),
      realizedCoverageAvg impl adv claim ≥ claim.alpha + F.slackFn σ bp := by
  have heta : 0 ≤ F.eta 1 := F.eta_nonneg 1
  set σ := 1 / (4 * (F.eta 1 + 1)) with hσ_def
  have hσ : 0 < σ := by rw [hσ_def]; positivity
  refine ⟨σ, hσ, bp10, mkImpl σ hσ, mkInv σ hσ, mkAdv σ hσ,
    ⟨1/2, 0, by norm_num, by norm_num⟩, ?_⟩
  rw [coverage_is_one]
  unfold AdmissibleFamily.slackFn
  simp only [bp10, zpow_neg, zpow_natCast, pow_zero, inv_one]
  rw [hσ_def]
  have key : F.eta 1 * (1 / (4 * (F.eta 1 + 1))) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 4)]
    nlinarith
  linarith

/-!
## `MasterLowerValidAvgUniv` — the lower clause closes

The lower clause of `MasterSharpSlackAvgUniv` is a direct consequence
of `lower_pigeonhole_adversary`.
-/
theorem MasterLowerValidAvgUniv_holds (F : AdmissibleFamily) :
    MasterLowerValidAvgUniv F :=
  lower_pigeonhole_adversary F

/-!
## `MasterSharpSlackAvgUniv` — the conjunction is FALSE

The upper clause `MasterUpperValidAvgUniv F` is false for every `F`
(see `not_MasterUpperValidAvgUniv`), so the conjunction is false.
This is a consequence of the vacuous sub-Gaussian formalization.
-/

/- ORIGINAL STATEMENT (commented out — false, upper clause refuted):

theorem MasterSharpSlackAvgUniv_from_decomposition (F : AdmissibleFamily) :
    MasterUpperValidAvgUniv F ∧ MasterLowerValidAvgUniv F := by
  refine ⟨?_, ?_⟩
  · intro σ hσ bp impl inv adv claim
    exact averaged_upper_from_mgf F σ hσ bp impl inv adv claim
  · exact lower_pigeonhole_adversary F

The composition is blocked because `averaged_upper_from_mgf` is false.
The lower half is proven: see `MasterLowerValidAvgUniv_holds`.
-/

/-- **`MasterSharpSlackAvgUniv` is false** for every admissible family.
The upper clause `MasterUpperValidAvgUniv F` is refuted by the same
`bits=1, scale=0` construction: `SubGaussianMartingale.subGaussian`
is vacuous, so adversaries can force `realizedCoverageAvg = 1` while
`α + F.slackFn < 1` for small σ. -/
theorem not_MasterSharpSlackAvgUniv (F : AdmissibleFamily) :
    ¬ (MasterUpperValidAvgUniv F ∧ MasterLowerValidAvgUniv F) := by
  intro ⟨h_upper, _⟩
  exact not_MasterUpperValidAvgUniv F h_upper

end HowardBridge
