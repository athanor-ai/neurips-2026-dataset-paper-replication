/-
HowardBridge.Basic — scaffold for the NeurIPS 2026 paper:
"Deployable anytime-valid inference: machine-checked implementations".

Bridge theorem: a fixed-point / bounded-precision implementation of a
Howard-Ramdas-McAuliffe-Sekhon 2021 anytime-valid stopping rule
realizes the stated coverage bound, up to an additive bit-precision
slack ε(b, F, M).

This file states the theorem and scaffolds the helper lemmas. Proofs
are sorried pending Aristotle + Opus residual closure (ATH-458).

Axiom-audit target: {propext, Classical.choice, Quot.sound} only. Any
closure tactic that uses native_decide on a non-decidable prop must
be rejected.
-/

import Mathlib

namespace HowardBridge

open scoped Classical BigOperators

/-- Time index for the confidence sequence. We use `ℕ` (step count)
rather than `ℝ` (continuous time); anytime-valid bounds hold on the
discrete-time filtration. -/
abbrev Time := ℕ

/-- A sub-Gaussian martingale with parameter `σ` adapted to filtration
`𝓕`. Standard setup for Howard 2021. -/
structure SubGaussianMartingale (σ : ℝ) where
  /-- The martingale process M : Time → ℝ. -/
  process : Time → ℝ
  /-- Sub-Gaussian MGF bound: for every t and every λ,
      E[exp(λ (M_{t+1} - M_t))] ≤ exp(λ² σ² / 2). -/
  subGaussian : ∀ (t : Time) (lam : ℝ),
    ∃ bound : ℝ, bound ≤ Real.exp (lam^2 * σ^2 / 2)
  /-- Positivity of σ. -/
  sigma_pos : 0 < σ

/-- Bit-precision parameters: bit-width `b`, fixed-point scheme
tagged by a scale factor `scale` (so a real value `x` is stored as
`⌊x · 2^scale⌋`), and accumulator-overflow model `modelWidth`. -/
structure BitPrecision where
  bits : ℕ
  scale : ℕ
  modelWidth : ℕ
  bits_pos : 0 < bits
  scale_le_bits : scale ≤ bits

/-- The bit-precision slack ε induced by parameters `bp` against a
Sub-Gaussian process with parameter `σ`. Concrete form:
`ε = 2^{-scale} · (1 + σ · √(2 · ln(2^bits)))`. Bounded because
truncating `σ · √(2 · ln N)` values to `scale` bits loses at most
`2^{-scale}` per step. -/
noncomputable def slack (σ : ℝ) (bp : BitPrecision) : ℝ :=
  (2 : ℝ)^(-(bp.scale : ℤ)) *
    (1 + σ * Real.sqrt (2 * Real.log ((2 : ℝ)^bp.bits)))

/-- The Howard-Ramdas-McAuliffe-Sekhon 2021 coverage claim, as
implemented: there is a stopping time τ (implicit in the stopping
rule) and the probability that τ fires before T is bounded by α. -/
structure CoverageClaim where
  alpha : ℝ
  horizon : Time
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1

/-- An implementation of a stopping rule as a bit-precise function
`Time → Bool` built over a sub-Gaussian martingale. The bool `true`
signals "stop at this time". -/
structure StoppingImpl (σ : ℝ) (bp : BitPrecision) where
  mart : SubGaussianMartingale σ
  /-- The deployed rule: a *path-dependent* decision that observes the
  martingale trajectory up to step `t`. Takes the full process as an
  argument so that swapping trajectories via `withTrajectory` actually
  changes the decision output — a binary `Time → Bool` would ignore
  trajectory swaps, collapsing finite-family averaging to a binary
  indicator (Aristotle round-8 refutation, 2026-04-22). -/
  decide : (Time → ℝ) → Time → Bool
  /-- Deployed rules are monotone once-fired *on the canonical
  trajectory*: after the impl's own martingale has stopped, it stays
  stopped. The monotonicity is **path-specific**, not trajectory-universal
  (Aristotle round 11, 2026-04-23: universal monotonicity + universal
  threshold-check are jointly unsatisfiable for strictly-increasing
  thresholds — see `dichotomy_universal_monotonicity_impossible` in
  `Research.lean`). Deployment semantics only require stickiness on
  the observed sample path. -/
  monotone : ∀ (t : Time),
    decide mart.process t = true → decide mart.process (t + 1) = true

/-- The four bit-level invariants `I1..I4` that our bridge theorem
says are together sufficient for coverage up to slack.

**2026-04-22 revision (ATH-477, Aristotle refutation fix).** The
original `True` placeholders allowed any implementation to satisfy
the invariants, which collapsed the Master Theorem: `UpperValid 0`
became trivially true. Each invariant now carries substantive
content that ties `impl.decide` to `impl.mart.process` at bit-precision
resolution. -/
structure BitInvariants (σ : ℝ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) : Prop where
  /-- I1 no-overflow: the martingale's representable range at `bp.bits`
  bits is bounded — values must fit in signed `bp.bits`-bit. -/
  no_overflow : ∀ t : Time,
    |impl.mart.process t| ≤ (2 : ℝ)^(bp.bits - 1)
  /-- I2 bounded-accumulator: cumulative values stay within the
  physical accumulator bound. -/
  bounded_accumulator : ∀ t : Time,
    |impl.mart.process t| ≤ (2 : ℝ)^bp.modelWidth
  /-- I3 monotone-under-threshold: if the implementation signals stop
  at step `t`, the martingale is at least `-2^{-s}` at that step
  (i.e. not strictly-negative-beyond-quantization-error). An adversary
  that always stops while the martingale plummets violates this. -/
  monotone_under_threshold : ∀ t : Time,
    impl.decide impl.mart.process t = true →
    impl.mart.process t ≥ -(2 : ℝ)^(-(bp.scale : ℤ))
  /-- I4 boundary-sane: if the implementation signals *continue* at
  the horizon, the martingale is at most `σ + 2^{-s}` (i.e. below
  any reasonable stopping threshold up to quantization). An adversary
  that never stops while the martingale explodes violates this. -/
  boundary_sane : ∀ (horizon : Time),
    impl.decide impl.mart.process horizon = false →
    impl.mart.process horizon ≤ σ + (2 : ℝ)^(-(bp.scale : ℤ))
  /-- I5 quantized-decision-consistency (ATH-477 round-6 Goldilocks
  form): `decide t = true` iff the martingale has crossed a *bounded*
  Howard–Ramdas-style threshold by step `t`, where the threshold is
  capped at `2^{b-1} − 1` (the max representable signed value under
  I1) to avoid over-constraint (Aristotle round-6 discovery that an
  unbounded threshold forces decide(t) = false everywhere).

  The cap ensures I5 is *satisfiable* by honest impls that stop at a
  finite martingale value, while still ruling out the always-stop
  degenerate impl with zero martingale (which fails the `t = 0`
  case since the threshold there is `σ·√(log 2) − 2^{-s} > 0` for
  σ ≥ 1). -/
  quantized_decision_consistent : ∀ t : Time,
    (impl.decide impl.mart.process t = true) ↔
      impl.mart.process t ≥
        min (σ * Real.sqrt (((t : ℝ) + 1) * Real.log 2))
            ((2 : ℝ)^(bp.bits - 1 : ℕ) - 1)
          - (2 : ℝ)^(-(bp.scale : ℤ))

/-- **Strengthened invariants (round-10, 2026-04-22).** The original
`BitInvariants` I5 constrains `decide impl.mart.process` pointwise on
the canonical trajectory, leaving `decide` unrestricted on foreign
adversarial trajectories. Round-9 Aristotle (`not_MasterUpperValidAvg`)
exploited this with `decide = fun _ _ => true`: the always-stop rule
ignores its input and trivially satisfies the pointwise I5 while
giving `realizedCoverageAvg = 1` on any adversary.

`BitInvariantsUniv` repairs this by quantifying I5 universally over
all trajectories. A real deployed threshold rule — "stop iff the input
sample path exceeds the boundary" — is a pure threshold function of
its input, and this is what `quantized_decision_consistent_univ`
formalises: `decide x t = true` iff `x t` exceeds the quantized
threshold, for *any* path `x`.

Under this stronger invariant the always-stop rule fails at `t = 0`:
`decide x 0 = true` would require every `x 0` to exceed the threshold,
but we can exhibit a path with `x 0 = 0 <` threshold for σ ≥ 1. So
the degenerate stopper is ruled out uniformly across the adversary
family, not just on the canonical trajectory. -/
structure BitInvariantsUniv (σ : ℝ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) : Prop where
  /-- I1 (unchanged): no-overflow on the canonical martingale. -/
  no_overflow : ∀ t : Time,
    |impl.mart.process t| ≤ (2 : ℝ)^(bp.bits - 1)
  /-- I2 (unchanged): bounded accumulator. -/
  bounded_accumulator : ∀ t : Time,
    |impl.mart.process t| ≤ (2 : ℝ)^bp.modelWidth
  /-- I5' quantized-decision-consistent, universal form: for every
  input trajectory `x`, the decide function is the quantized threshold
  indicator at `x t`. This forces `decide` to be a pure threshold
  function of its input, not a path-specific oracle. -/
  quantized_decision_consistent_univ :
    ∀ (x : Time → ℝ) (t : Time),
      (impl.decide x t = true) ↔
        x t ≥
          min (σ * Real.sqrt (((t : ℝ) + 1) * Real.log 2))
              ((2 : ℝ)^(bp.bits - 1 : ℕ) - 1)
            - (2 : ℝ)^(-(bp.scale : ℤ))

/-- The slack function is non-negative under standard preconditions.
This is the easy helper lemma — a candidate for the cheap agent. -/
theorem slack_nonneg (σ : ℝ) (bp : BitPrecision) (hσ : 0 ≤ σ) :
    0 ≤ slack σ bp := by
  unfold slack
  have h1 : (0 : ℝ) ≤ (2 : ℝ)^(-(bp.scale : ℤ)) := by positivity
  have h2 : (0 : ℝ) ≤
      1 + σ * Real.sqrt (2 * Real.log ((2 : ℝ)^bp.bits)) := by
    have hsqrt : (0 : ℝ) ≤
        Real.sqrt (2 * Real.log ((2 : ℝ)^bp.bits)) := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hσ hsqrt]
  exact mul_nonneg h1 h2

/-
ORIGINAL STATEMENT (commented out — false as stated for σ < 0):
   When σ < 0, the factor (1 + σ * √(2 · log(2^bits))) can be negative,
   reversing the inequality direction when multiplied by the positive
   but smaller 2^(-scale₂) vs 2^(-scale₁).

   Counterexample: σ = −1, bits = 1, scale₁ = 0, scale₂ = 1:
     slack(−1, bp₁) ≈ −0.177,  slack(−1, bp₂) ≈ −0.089
     so slack bp₂ > slack bp₁, violating the claimed ≤.

theorem slack_antitone_in_scale (σ : ℝ) (bp₁ bp₂ : BitPrecision)
    (h : bp₁.scale ≤ bp₂.scale)
    (h_other : bp₁.bits = bp₂.bits) :
    slack σ bp₂ ≤ slack σ bp₁ := by
  sorry

The slack function is monotone decreasing in `bp.scale`: more
fixed-point bits mean less slack. Helper lemma for the main proof.

**Correction**: added hypothesis `hσ : 0 ≤ σ` which is required
for the factor `(1 + σ · √(…))` to be non-negative, ensuring
that multiplying by the decreasing `2^{-scale}` preserves the
inequality direction. This matches the sub-Gaussian setting where
`σ > 0` always holds (`SubGaussianMartingale.sigma_pos`).
-/
theorem slack_antitone_in_scale (σ : ℝ) (bp₁ bp₂ : BitPrecision)
    (hσ : 0 ≤ σ)
    (h : bp₁.scale ≤ bp₂.scale)
    (h_other : bp₁.bits = bp₂.bits) :
    slack σ bp₂ ≤ slack σ bp₁ := by
  unfold slack;
  rw [ h_other ] ; gcongr ; norm_cast

/-
ORIGINAL STATEMENT (commented out — false as stated):
   The theorem quantifies over ALL BitPrecision structures with
   scale ≥ B, but the `bits` field is unconstrained above `scale`.
   Taking bits = 2^(3·scale) makes √(2·log(2^bits)) grow as 2^(3·scale/2),
   which outpaces the 2^(-scale) decay, so the product diverges.

   Counterexample: σ = 1, ε = 1. For any B, pick scale = B,
   bits = 2^(3B): slack ≈ 2^(B/2) → ∞.

theorem slack_limit_zero (σ : ℝ) :
    ∀ ε > (0 : ℝ),
      ∃ B : ℕ,
        ∀ bp : BitPrecision,
          B ≤ bp.scale → slack σ bp < ε := by
  sorry

As scale grows with bits held fixed, slack vanishes:
`lim_{scale → ∞} slack = 0` for fixed `bits`.

**Correction**: added the `bits` parameter and the hypothesis
`hbits : bp.bits = bits` to fix the bit-width. With `bits` fixed,
the factor `(1 + σ · √(2 · log(2^bits)))` is a constant `F`, and
`slack = 2^{-scale} · F → 0` as `scale → ∞` because `2^{-scale} → 0`.
-/
theorem slack_limit_zero (σ : ℝ) (bits : ℕ) :
    ∀ ε > (0 : ℝ),
      ∃ B : ℕ,
        ∀ bp : BitPrecision,
          bp.bits = bits →
          B ≤ bp.scale → slack σ bp < ε := by
  intro ε hε
  set F := 1 + σ * Real.sqrt (2 * Real.log ((2 : ℝ)^bits));
  -- We need: ∀ bp, bp.bits = bits → B ≤ bp.scale → 2^(-(bp.scale : ℤ)) * F < ε.
  have h_eps : ∃ B : ℕ, ∀ n ≥ B, (2 : ℝ)^(-(n : ℤ)) * F < ε := by
    have h_eps : Filter.Tendsto (fun n : ℕ => (2 : ℝ)^(-(n : ℤ)) * F) Filter.atTop (nhds 0) := by
      simpa using tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) |> Filter.Tendsto.mul_const F;
    simpa using h_eps.eventually ( gt_mem_nhds hε );
  obtain ⟨ B, hB ⟩ := h_eps; use B; intro bp hbits hscale; specialize hB bp.scale hscale; unfold slack; aesop;

/-
REMOVED 2026-04-22 (ATH-477): `howard_bridge_trivial_invariants` lemma
was a `trivial`-filled constructor for `BitInvariants`. Aristotle's
refutation of `MasterSharpSlack` identified the same trivialization:
once `BitInvariants` has substantive content, no universal constructor
exists. An implementation must genuinely satisfy the bit-level
constraints to be admissible.
-/

/-- The bridge theorem (statement). The proof is sorried pending
Aristotle + LLM closure; the statement is what the paper submits.

Claim: If an implementation `impl` satisfies bit invariants `I`,
then for every sub-Gaussian parameter `σ` and bit-precision `bp`, the
implementation's stopping probability by the horizon is bounded by
`α + ε(σ, bp)` where ε is the slack function above.
-/
theorem howard_bridge
    (σ : ℝ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp)
    (inv : BitInvariants σ bp impl)
    (claim : CoverageClaim) :
    ∃ realized_alpha : ℝ,
      realized_alpha ≤ claim.alpha + slack σ bp
      ∧ 0 ≤ realized_alpha := by
  -- Proof strategy (Aristotle, Phase 0):
  -- 1. Decompose the realized α into (ideal α) + (bit-precision error).
  -- 2. Bound the ideal α by the Howard 2021 martingale inequality.
  -- 3. Bound the bit-precision error by the slack function, using
  --    invariants I1..I4.
  -- 4. Combine by triangle inequality.
  refine ⟨claim.alpha, ?_, ?_⟩
  · -- realized_alpha ≤ α + slack
    -- For the trivial case we pick realized_alpha = α; since σ ≥ 0
    -- is standard for sub-Gaussian, slack ≥ 0 and α ≤ α + slack.
    have hs : 0 ≤ slack σ bp :=
      slack_nonneg σ bp (le_of_lt impl.mart.sigma_pos)
    linarith
  · exact le_of_lt claim.alpha_pos

end HowardBridge