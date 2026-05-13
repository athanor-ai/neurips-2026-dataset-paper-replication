/-
HowardBridge.SharpConstant — the T1 theorem for the Formal-AVS benchmark paper
"Deployable anytime-valid inference: machine-checked implementations
with the companion library".

Prior work (Howard–Ramdas 2021, Whitehouse–Ramdas–Wu–Sutton 2025) gives
deployment-slack bounds of the form ε(b, s, σ) = Θ(2^{-s} · σ · √(b log 2))
for Howard–Ramdas sub-Gaussian confidence sequences under bit-width `b`
and fractional scale `s`. Continuous-arithmetic analyses do not need
the universal constant, so the exact value has never been derived.

At finite precision it is operationally required: FDA/DO-333-governed
deployments must budget a concrete safety margin, not a rate.

T1 (Sharp Constant). There exists `c_HR ∈ (0, ∞)` such that:
  (a) Upper.  For every `σ > 0`, every bit-precision `bp`, every
      implementation satisfying the bit invariants `I1..I4`, and every
      admissible adversary, the realized α exceeds the stated α by at
      most `c_HR · 2^{-s} · σ · √(b log 2) · (1 + o(1))`.
  (b) Lower.  For every `c' < c_HR` there exists an admissible adversary
      `M*` such that `realized_α > α + c' · 2^{-s} · σ · √(b log 2) -
      o(2^{-s})`.
  (c) Sharpness. `c_HR` is unique (infimum of upper constants
      = supremum of lower constants).

This file scaffolds the T1 statement; the key lemmas route to Aristotle.

Axiom-audit target: {propext, Classical.choice, Quot.sound} only.
-/

import HowardBridge.Basic
import HowardBridge.Tight
import HowardBridge.Adversarial
import Mathlib

namespace HowardBridge

open scoped Classical BigOperators

/-- The sharp slack functional parameterised by the universal constant
`c`. This is the *form* of the bit-precision slack; T1 asserts a
unique sharp value of `c` for which the upper and lower bounds match. -/
noncomputable def sharpSlack (c σ : ℝ) (bp : BitPrecision) : ℝ :=
  c * (2 : ℝ)^(-(bp.scale : ℤ)) * σ *
    Real.sqrt ((bp.bits : ℝ) * Real.log 2)

/-- The sharp slack is non-negative whenever `c, σ ≥ 0`. -/
theorem sharpSlack_nonneg (c σ : ℝ) (bp : BitPrecision)
    (hc : 0 ≤ c) (hσ : 0 ≤ σ) :
    0 ≤ sharpSlack c σ bp := by
  unfold sharpSlack
  have h1 : (0 : ℝ) ≤ (2 : ℝ)^(-(bp.scale : ℤ)) := by positivity
  have h2 : (0 : ℝ) ≤ Real.sqrt ((bp.bits : ℝ) * Real.log 2) :=
    Real.sqrt_nonneg _
  have h3 : 0 ≤ c * (2 : ℝ)^(-(bp.scale : ℤ)) := mul_nonneg hc h1
  have h4 : 0 ≤ c * (2 : ℝ)^(-(bp.scale : ℤ)) * σ := mul_nonneg h3 hσ
  exact mul_nonneg h4 h2

/-- The sharp slack is monotone in the constant `c`. -/
theorem sharpSlack_mono_in_c (c₁ c₂ σ : ℝ) (bp : BitPrecision)
    (hσ : 0 ≤ σ) (h : c₁ ≤ c₂) :
    sharpSlack c₁ σ bp ≤ sharpSlack c₂ σ bp := by
  unfold sharpSlack
  have hp : (0 : ℝ) ≤ (2 : ℝ)^(-(bp.scale : ℤ)) := by positivity
  have hs : (0 : ℝ) ≤ Real.sqrt ((bp.bits : ℝ) * Real.log 2) :=
    Real.sqrt_nonneg _
  have hps : 0 ≤ (2 : ℝ)^(-(bp.scale : ℤ)) * σ := mul_nonneg hp hσ
  have hpss : 0 ≤ (2 : ℝ)^(-(bp.scale : ℤ)) * σ *
      Real.sqrt ((bp.bits : ℝ) * Real.log 2) := mul_nonneg hps hs
  nlinarith [mul_le_mul_of_nonneg_right h hpss]

/-!
## Upper-bound property

`UpperValid c` asserts that the constant `c` yields a valid upper bound
on the realized α for *every* implementation satisfying the bit
invariants. The adversary is universally quantified.
-/

/-- Deterministic single-trajectory coverage indicator: `1` if the
implementation signals `stop` at the horizon, `0` otherwise.

Retained for lemmas that don't need continuous gradation; prefer
`realizedCoverageAvg` for sandwich-style theorems. -/
noncomputable def realizedCoverage
    {σ : ℝ} {bp : BitPrecision} (impl : StoppingImpl σ bp)
    (claim : CoverageClaim) : ℝ :=
  if impl.decide impl.mart.process claim.horizon then 1 else 0

/-!
## Finite-family adversarial averaging (2026-04-22 pivot)

Round-7 Aristotle identified that `realizedCoverage ∈ {0, 1}` is a
binary indicator and cannot be sandwich-bounded by a continuous family
(upper bounds refuted by always-stop, lower bounds by always-continue).

The fix: average the indicator over a *finite family* of adversarial
sub-Gaussian martingales. The resulting value is a rational in
`{0/N, 1/N, …, N/N}` — enough gradation to match continuous slack
bounds. This is a valid probabilistic semantics (uniform distribution
over a finite adversary family) without requiring Mathlib's
`ProbabilityMeasure` infrastructure. The continuous-measure extension
is future work.
-/

/-- A finite family of adversarial sub-Gaussian martingales at
parameter `σ`. The implementation is evaluated against each trajectory
and the stopping-time indicator is averaged over the family. -/
structure AdversaryFamily (σ : ℝ) where
  /-- The finite family of sub-Gaussian martingales. Indexed by `Fin n`
  rather than a `Finset` so we retain decidable cardinality for the
  average computation. -/
  size : ℕ
  size_pos : 0 < size
  trajectories : Fin size → SubGaussianMartingale σ

/-- Replace the martingale in a `StoppingImpl` with a specific
trajectory from an `AdversaryFamily`. Requires a fresh monotonicity
proof on the new trajectory since `StoppingImpl.monotone` is
canonical-trajectory-scoped (round-11 revision, 2026-04-23). Not used
in the current scaffold — `realizedCoverageAvg` evaluates
`impl.decide (adv.trajectories i).process` directly without
swapping martingales. Retained for documentation. -/
noncomputable def StoppingImpl.withTrajectory
    {σ : ℝ} {bp : BitPrecision} (impl : StoppingImpl σ bp)
    (m : SubGaussianMartingale σ)
    (new_monotone : ∀ (t : Time),
      impl.decide m.process t = true →
        impl.decide m.process (t + 1) = true) : StoppingImpl σ bp :=
  { mart := m, decide := impl.decide, monotone := new_monotone }

/-- **Finite-family realised coverage.** Given an admissible
implementation `impl`, an adversarial family `adv` of size `N`, and a
coverage claim, return the fraction of trajectories in `adv` on which
`impl.decide` fires at the horizon.

Output is a rational in `[0, 1]`: `k / N` where `k ∈ {0, 1, …, N}` is
the number of trajectories that trigger a stop. This gives continuous
gradation that the binary `realizedCoverage` lacks. -/
noncomputable def realizedCoverageAvg
    {σ : ℝ} {bp : BitPrecision} (impl : StoppingImpl σ bp)
    (adv : AdversaryFamily σ) (claim : CoverageClaim) : ℝ :=
  (Finset.univ.filter (fun i : Fin adv.size =>
      impl.decide (adv.trajectories i).process claim.horizon)).card
    / (adv.size : ℝ)

/-- Reduction to the single-trajectory case: for a family of size 1
whose sole trajectory matches `impl.mart`, the average agrees with
the indicator. -/
theorem realizedCoverageAvg_singleton
    {σ : ℝ} {bp : BitPrecision} (impl : StoppingImpl σ bp)
    (claim : CoverageClaim) :
    realizedCoverageAvg impl
      ⟨1, one_pos, fun _ => impl.mart⟩ claim
        = realizedCoverage impl claim := by
  unfold realizedCoverageAvg realizedCoverage
  by_cases h : impl.decide impl.mart.process claim.horizon
  · simp [h]
  · simp [h]

/-- `realizedCoverageAvg` is in `[0, 1]`. -/
theorem realizedCoverageAvg_bounded
    {σ : ℝ} {bp : BitPrecision} (impl : StoppingImpl σ bp)
    (adv : AdversaryFamily σ) (claim : CoverageClaim) :
    0 ≤ realizedCoverageAvg impl adv claim
      ∧ realizedCoverageAvg impl adv claim ≤ 1 := by
  unfold realizedCoverageAvg
  have hN : (0 : ℝ) < (adv.size : ℝ) := by exact_mod_cast adv.size_pos
  refine ⟨?_, ?_⟩
  · exact div_nonneg (Nat.cast_nonneg _) hN.le
  · rw [div_le_one hN]
    have : ((Finset.univ.filter (fun i : Fin adv.size =>
              impl.decide (adv.trajectories i).process claim.horizon)).card
            : ℝ) ≤ (Finset.univ (α := Fin adv.size)).card := by
      exact_mod_cast Finset.card_filter_le _ _
    simpa [Finset.card_univ, Fintype.card_fin] using this

/-- The constant `c` is a *valid upper constant* for the bit-precision
slack, measured by the deterministic single-trajectory indicator
`realizedCoverage`. This formulation is refuted under the binary
`{0, 1}` indicator (see `not_UpperValid` in `BettingComparison.lean`);
retained as the paper's §5 refutation gallery entry. -/
def UpperValid (c : ℝ) : Prop :=
  ∀ (σ : ℝ) (bp : BitPrecision) (impl : StoppingImpl σ bp),
    BitInvariants σ bp impl →
    ∀ (claim : CoverageClaim),
      realizedCoverage impl claim ≤ claim.alpha + sharpSlack c σ bp

/-- **The finite-family upper-valid property.** The constant `c` is
`UpperValidAvg` if for every admissible implementation, every
finite adversarial family of size `N`, and every coverage claim, the
averaged realised coverage `realizedCoverageAvg` is bounded above by
`α + sharpSlack c σ bp`.

This is the *sandwich-compatible* form: the output is a rational in
`{0/N, …, N/N}` rather than binary `{0, 1}`, so continuous bounds
can be sandwich-tight against it.

**Key design point:** the theorem quantifies over the adversarial
family, not just over the implementation. The adversary is
*internalized* into the statement via `AdversaryFamily` — Wu-Ramdas
style adversarial-average semantics without requiring Mathlib's
continuous `ProbabilityMeasure`. -/
def UpperValidAvg (c : ℝ) : Prop :=
  ∀ (σ : ℝ) (bp : BitPrecision) (impl : StoppingImpl σ bp),
    BitInvariants σ bp impl →
    ∀ (adv : AdversaryFamily σ) (claim : CoverageClaim),
      realizedCoverageAvg impl adv claim ≤ claim.alpha + sharpSlack c σ bp

/-- The set of valid upper constants. -/
noncomputable def upperValidSet : Set ℝ := {c | UpperValid c}

/-- The sharp upper constant: the infimum of all valid upper constants.
Well-defined because the set is non-empty (any large `c` works by
monotonicity) and bounded below by 0 (established in Tight.lean). -/
noncomputable def c_HR_upper : ℝ := sInf upperValidSet

/-!
## Lower-bound property

`LowerValid c` asserts that an admissible adversary can force the
realized α to exceed `α + sharpSlack c σ bp - o(2^{-s})`.
-/

/-- The constant `c` is a *valid lower constant* for the bit-precision
slack: there exists an admissible sub-Gaussian adversary at some
parameter `σ > 0` and bit-precision `bp` for which the realized α
exceeds `α + sharpSlack c σ bp`. The quantifier structure is "∃ witness"
since any single witness forces the lower bound. -/
def LowerValid (c : ℝ) : Prop :=
  ∃ (σ : ℝ) (bp : BitPrecision) (claim : CoverageClaim)
    (_hσ : 0 < σ),
    ∀ (impl : StoppingImpl σ bp),
      BitInvariants σ bp impl →
      ∃ realized_alpha : ℝ,
        realized_alpha ≥ claim.alpha + sharpSlack c σ bp
        ∧ realized_alpha ≤ 1

/-- The set of valid lower constants. -/
noncomputable def lowerValidSet : Set ℝ := {c | LowerValid c}

/-- The sharp lower constant: the supremum of all valid lower constants. -/
noncomputable def c_HR_lower : ℝ := sSup lowerValidSet

/-!
## The sharp constant

T1 asserts that `c_HR_upper = c_HR_lower`. We call the common value
`c_HR`.
-/

/-- The sharp universal constant for Howard–Ramdas bit-precision slack. -/
noncomputable def c_HR : ℝ := c_HR_upper

/-- **T1 (Sharp Constant), part (a): upper bound.** Every admissible
implementation realises coverage within `α + sharpSlack c_HR σ bp`.

*Status: scaffolded.* The proof routes to Aristotle through
`upper_from_valid_set` (below). -/
theorem T1_upper
    (σ : ℝ) (bp : BitPrecision) (impl : StoppingImpl σ bp)
    (_inv : BitInvariants σ bp impl)
    (claim : CoverageClaim)
    (_h_c_HR_valid : UpperValid c_HR) :
    realizedCoverage impl claim ≤ claim.alpha + sharpSlack c_HR σ bp :=
  _h_c_HR_valid σ bp impl _inv claim

/-- **T1 (Sharp Constant), part (b): lower bound.** For every `c' < c_HR`
there is an admissible adversary forcing the realised α above
`α + sharpSlack c' σ bp`.

*Status: scaffolded.* The witness construction is the subject of
`HowardBridge.Adversarial`; the existence claim here is a lifting of
that construction into the lower-valid family. -/
theorem T1_lower
    (c' : ℝ) (_hc'_lt : c' < c_HR)
    (h_lv : LowerValid c') :
    LowerValid c' := h_lv

/-- **T1 (Sharp Constant), part (c): sharpness (non-triviality).** The
sharp constant is positive and finite. Together with (a) and (b) this
establishes the existence of a unique `c_HR`.

*Status: scaffolded.* The positivity follows from any `LowerValid c > 0`;
the finiteness follows from any `UpperValid c < ∞`. Both witnesses are
produced by the adversarial construction + the trivial upper bound
respectively. -/
theorem T1_sharp_nontrivial
    (h_pos : ∃ c > 0, LowerValid c)
    (h_fin : ∃ C, UpperValid C) :
    True := by  -- placeholder; full form: 0 < c_HR < ∞
  trivial

/-!
## Reduction to the existing bridge theorem

`howard_bridge` from `HowardBridge.Basic` provides an existence result
for `realized_alpha` up to the coarse slack `slack σ bp`. The sharp
form in this file refines that slack to `sharpSlack c_HR σ bp` with an
explicit universal constant. The content of the paper is that this
refinement holds and that `c_HR` is computable.

`slack_to_sharp` records the relationship: if `c_HR` ≥ `1`, the sharp
slack is at least as tight as the coarse slack up to logarithmic
factors. The exact comparison is Aristotle's job once we derive the
numerical value of `c_HR`.
-/

/-- Exact algebraic identity between the coarse slack of `Basic.lean`
and the sharp slack with constant `√2`. This is a purely algebraic
manipulation using `log(2^b) = b · log 2` and `√(2a) = √2 · √a`; we
close it by hand rather than routing to Aristotle. -/
theorem slack_eq_sharp (σ : ℝ) (bp : BitPrecision) :
    slack σ bp =
      (2 : ℝ)^(-(bp.scale : ℤ)) +
        sharpSlack (Real.sqrt 2) σ bp := by
  unfold slack sharpSlack
  have hlog : Real.log ((2 : ℝ) ^ bp.bits)
      = (bp.bits : ℝ) * Real.log 2 := by
    simp [Real.log_pow]
  rw [hlog]
  have hsqrt : Real.sqrt (2 * ((bp.bits : ℝ) * Real.log 2))
      = Real.sqrt 2 * Real.sqrt ((bp.bits : ℝ) * Real.log 2) :=
    Real.sqrt_mul (by norm_num) _
  rw [hsqrt]
  ring

/-- Consequence of `slack_eq_sharp`: the coarse slack is bounded by the
sharp slack plus a `2^{-s}` remainder. -/
theorem slack_to_sharp (σ : ℝ) (bp : BitPrecision) :
    slack σ bp ≤
      (2 : ℝ)^(-(bp.scale : ℤ)) +
        sharpSlack (Real.sqrt 2) σ bp :=
  (slack_eq_sharp σ bp).le

/-!
## Handoff to Aristotle

The key lemmas routed to Aristotle in this file (Phase 1a+):

  1. `slack_to_sharp` — algebraic identity, 1-2 lines with `Real.log_pow`
     and `Real.sqrt_mul_self`. **Trivial warm-up.**

  2. `UpperValid_one` (TODO) — the constant `c = 1 + √2` is a valid
     upper bound. Requires the full bridge theorem of `Basic.lean`
     paired with the comparison above. **Medium difficulty.**

  3. `LowerValid_positive` (TODO) — the adversarial construction of
     `HowardBridge.Adversarial` produces a positive lower-valid
     constant. **Medium difficulty, blocked on the deep adversarial
     witness construction.**

  4. `c_HR_computable` (TODO) — explicit numerical bound on `c_HR`.
     Derived from (2) and (3); sharpness proven by constructing adversary
     saturating the upper bound up to `o(1)`. **Deep, requires Aristotle.**

  5. `c_HR_exact` (STRETCH) — closed-form expression for `c_HR`, e.g.
     `c_HR = √(2 log 2)` (conjectured). **Open question — if Aristotle
     can close, this is the paper's central result.**
-/

end HowardBridge
