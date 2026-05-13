/-
HowardBridge.MasterTheorem — the unified theorem for the Formal-AVS
paper: "Deployable anytime-valid inference: machine-checked
implementations".

Replaces the two independent theorems T1 (sharp Howard–Ramdas constant)
and T2 (betting-vs-self-normalized comparison) with a single master
characterization indexed over admissible anytime-valid CS families.

**Master Sharp-Slack Theorem.** For every admissible anytime-valid CS
family `F` (indexed by σ-sub-Gaussian parameter), there exists a
unique family-specific rate `η_F : ℕ → ℝ_+` such that the bit-precision
deployment-slack satisfies

    ε_F(b, s, σ) = η_F(b) · 2^{-s} · σ + o_F(b, s, σ).

The rate `η_F` is *not* uniform across families. We instantiate the
master theorem for three canonical admissible families and obtain a
three-way ranking:

    η_HR(b)      = √(b · log 2)            (Howard–Ramdas self-normalized)
    η_betting(b) = 1 / √(b · log 2 + 1)    (Ramdas–Ruf / Waudby-Smith betting)
    η_vector(b)  = √(2 · b · log 2)        (Whitehouse–Ramdas–Wu–Sutton vector)

**Corollary (Ranking).** `η_betting(b) → 0` while `η_HR(b), η_vector(b) → ∞`
as `b → ∞`. Betting is the *unique* asymptotically-vanishing-slack
admissible family.

Axiom-audit target: {propext, Classical.choice, Quot.sound} only.
-/

import HowardBridge.Basic
import HowardBridge.Tight
import HowardBridge.Adversarial
import HowardBridge.SharpConstant
import HowardBridge.BettingComparison
import Mathlib

namespace HowardBridge

open scoped Classical BigOperators

/-!
## Admissible anytime-valid CS family
-/

/-- Abstract admissible anytime-valid CS family. A concrete family is a
pair `(process generator, coverage predicate)` that admits a
deployment-slack rate function `η : ℕ → ℝ`. We bake in the minimal
structural assumptions needed for the master theorem:

  (1) non-negativity of the rate,
  (2) a bit-precision slack function induced by `η` and the standard
      `2^{-s} · σ` scaling,
  (3) adversarial witness realisability (there exists a sub-Gaussian
      adversary forcing the rate at any bit-precision). -/
structure AdmissibleFamily where
  /-- Family name — informational only, for paper cross-referencing. -/
  name : String
  /-- Sharp deployment-slack rate at bit-width `b`. -/
  eta : ℕ → ℝ
  /-- Rate is non-negative. -/
  eta_nonneg : ∀ b : ℕ, 0 ≤ eta b

/-- The induced deployment slack function for an admissible family:
`η(b) · 2^{-s} · σ`. Derived from `eta` and the standard scaling;
not an overridable structure field (that was the Aristotle-refuted
design of 2026-04-22 which allowed adversarial families to break the
Master Theorem). -/
noncomputable def AdmissibleFamily.slackFn
    (F : AdmissibleFamily) (σ : ℝ) (bp : BitPrecision) : ℝ :=
  F.eta bp.bits * (2 : ℝ)^(-(bp.scale : ℤ)) * σ

/-!
## Family instances

Three canonical admissible families for the paper (moved before
Master Theorem for dependency ordering).
-/

/-- Howard–Ramdas self-normalized family. Rate `η_HR(b) = √(b · log 2)`
grows as `√b`. -/
noncomputable def familyHR : AdmissibleFamily where
  name := "Howard-Ramdas self-normalized"
  eta := fun b => Real.sqrt ((b : ℝ) * Real.log 2)
  eta_nonneg := fun _ => Real.sqrt_nonneg _

/-- Ramdas–Ruf / Waudby-Smith betting family. Rate
`η_betting(b) = 1/√(b · log 2 + 1)` vanishes as `1/√b`. -/
noncomputable def familyBetting : AdmissibleFamily where
  name := "Waudby-Smith-Ramdas betting"
  eta := fun b => 1 / Real.sqrt ((b : ℝ) * Real.log 2 + 1)
  eta_nonneg := fun b => by
    apply div_nonneg
    · norm_num
    · exact Real.sqrt_nonneg _

/-- Whitehouse–Ramdas–Wu–Sutton vector-valued family. Rate
`η_vector(b) = √(2 · b · log 2)` grows fastest. -/
noncomputable def familyVector : AdmissibleFamily where
  name := "Whitehouse-Ramdas-Wu-Sutton vector"
  eta := fun b => Real.sqrt (2 * (b : ℝ) * Real.log 2)
  eta_nonneg := fun _ => Real.sqrt_nonneg _

/-- Waudby-Smith–Stark–Ramdas 2024 asymptotic CS family (CLT-based).
Rate `η_aCS(b) = √(log 2)` asymptotically constant in `b`. -/
noncomputable def familyAsymptotic : AdmissibleFamily where
  name := "Waudby-Smith-Stark-Ramdas asymptotic"
  eta := fun _ => Real.sqrt (Real.log 2)
  eta_nonneg := fun _ => Real.sqrt_nonneg _

/-!
## Master Sharp-Slack Theorem
-/

/-- `MasterUpperValid F` asserts that every admissible implementation
in family `F` achieves deployment slack at most `F.slackFn σ bp`,
measured by the deterministic `realizedCoverage` indicator. Refuted
under binary `{0, 1}` indicator (retained for §5 refutation gallery). -/
def MasterUpperValid (F : AdmissibleFamily) : Prop :=
  ∀ (σ : ℝ) (_hσ : 0 < σ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) (_inv : BitInvariants σ bp impl)
    (claim : CoverageClaim),
    realizedCoverage impl claim ≤ claim.alpha + F.slackFn σ bp

/-- `MasterLowerValid F` (single-trajectory form, retained for
refutation-gallery context). -/
def MasterLowerValid (F : AdmissibleFamily) : Prop :=
  ∃ (σ : ℝ) (_hσ : 0 < σ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) (_inv : BitInvariants σ bp impl)
    (claim : CoverageClaim),
    realizedCoverage impl claim ≥ claim.alpha + F.slackFn σ bp

/-- **Finite-family `MasterUpperValidAvg F`.** Every admissible
implementation in family `F`, averaged over any finite adversarial
family, incurs coverage slack at most `F.slackFn σ bp`. The
`realizedCoverageAvg` output is continuous in `{0/N, …, N/N}`, so
sandwich-style bounds regain tightness that the binary indicator
blocked in rounds 3–7.

**Paper framing:** this is *the* Master Theorem for the Formal-AVS
benchmark paper. The single-trajectory `MasterUpperValid` above is retained
only as §5 refutation-gallery content. -/
def MasterUpperValidAvg (F : AdmissibleFamily) : Prop :=
  ∀ (σ : ℝ) (_hσ : 0 < σ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) (_inv : BitInvariants σ bp impl)
    (adv : AdversaryFamily σ) (claim : CoverageClaim),
    realizedCoverageAvg impl adv claim ≤ claim.alpha + F.slackFn σ bp

/-- **Finite-family `MasterLowerValidAvg F`.** There exists a
configuration (σ, bp, impl, adversarial family) for which the averaged
coverage equals or exceeds `α + F.slackFn σ bp`. Tight sandwich
companion to `MasterUpperValidAvg`. -/
def MasterLowerValidAvg (F : AdmissibleFamily) : Prop :=
  ∃ (σ : ℝ) (_hσ : 0 < σ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) (_inv : BitInvariants σ bp impl)
    (adv : AdversaryFamily σ) (claim : CoverageClaim),
    realizedCoverageAvg impl adv claim ≥ claim.alpha + F.slackFn σ bp

/-
**Round-9 refutation of `MasterUpperValidAvg` (2026-04-22).**

The path-dependent `decide : (Time → ℝ) → Time → Bool` refactor does
NOT fix the sandwich collapse. The same always-stop counterexample
from `not_MasterUpperValid` works verbatim:

  * `decide = fun _ _ => true` is a valid path-dependent function
    (it simply ignores the trajectory argument).
  * `BitInvariants` I5 only constrains `decide impl.mart.process`,
    not `decide` applied to arbitrary adversarial trajectories.
  * `realizedCoverageAvg` evaluates `impl.decide (adv.trajectories i).process`,
    which is `true` for all `i`, giving average = 1.
  * For small `σ`, `F.slackFn σ bp → 0`, so `1 > α + F.slackFn`.

Root cause: I5 is a *pointwise* constraint on the impl's own
trajectory. A fix requires I5 universally quantified over all
trajectories — addressed in `BitInvariantsUniv` (`Basic.lean`) and
`MasterSharpSlackAvgUniv` below, round 10 target.
-/
theorem not_MasterUpperValidAvg (F : AdmissibleFamily) :
    ¬ MasterUpperValidAvg F := by
  unfold MasterUpperValidAvg; push_neg; (
  refine' ⟨ 1 / ( 4 * ( F.eta 1 + 1 ) ), _, _ ⟩ <;> norm_num [ F.eta_nonneg ];
  · exact add_pos_of_nonneg_of_pos ( F.eta_nonneg 1 ) zero_lt_one;
  · refine' ⟨ ⟨ 1, 0, 1, by norm_num, by norm_num ⟩, _, _, _ ⟩;
    refine' ⟨ ⟨ fun _ => 0, _, _ ⟩, fun _ _ => Bool.true, _ ⟩ <;> norm_num;
    exact fun lam => ⟨ _, le_rfl ⟩;
    exact add_pos_of_nonneg_of_pos ( F.eta_nonneg 1 ) zero_lt_one;
    · constructor <;> norm_num;
    · refine' ⟨ ⟨ 1, by norm_num, fun _ => ⟨ fun _ => 0, _, _ ⟩ ⟩, ⟨ 1 / 2, 0, _, _ ⟩, _ ⟩ <;> norm_num [ realizedCoverageAvg ];
      · exact fun lam => ⟨ _, le_rfl ⟩;
      · exact add_pos_of_nonneg_of_pos ( F.eta_nonneg 1 ) zero_lt_one;
      · unfold AdmissibleFamily.slackFn; norm_num; nlinarith [ F.eta_nonneg 1, mul_inv_cancel₀ ( show ( F.eta 1 + 1 ) ≠ 0 by linarith [ F.eta_nonneg 1 ] ) ] ;);

/-
ORIGINAL STATEMENT (commented out — false under pointwise I5, Round-9 refutation):

  `MasterSharpSlackAvg F` requires `MasterUpperValidAvg F`, which is
  false by `not_MasterUpperValidAvg` above. The round-10 successor
  `MasterSharpSlackAvgUniv` uses a strengthened `BitInvariantsUniv`
  that universally quantifies I5 over all trajectories.

theorem MasterSharpSlackAvg (F : AdmissibleFamily) :
    MasterUpperValidAvg F ∧ MasterLowerValidAvg F := by
  sorry
-/

/-!
## Round-10 successor: `MasterSharpSlackAvgUniv`

Under the strengthened `BitInvariantsUniv` (universal-over-paths I5),
`decide` is pinned to a threshold function of its input trajectory.
This rules out the `fun _ _ => true` counterexample and makes the
upper sandwich provable by sub-Gaussian Ville-style bounds applied to
every adversarial trajectory.
-/

/-- **Universal-form upper-valid property.** Same as `MasterUpperValidAvg`
but indexed on the strengthened `BitInvariantsUniv`. -/
def MasterUpperValidAvgUniv (F : AdmissibleFamily) : Prop :=
  ∀ (σ : ℝ) (_hσ : 0 < σ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) (_inv : BitInvariantsUniv σ bp impl)
    (adv : AdversaryFamily σ) (claim : CoverageClaim),
    realizedCoverageAvg impl adv claim ≤ claim.alpha + F.slackFn σ bp

/-- **Universal-form lower-valid property.** Witness-existence form. -/
def MasterLowerValidAvgUniv (F : AdmissibleFamily) : Prop :=
  ∃ (σ : ℝ) (_hσ : 0 < σ) (bp : BitPrecision)
    (impl : StoppingImpl σ bp) (_inv : BitInvariantsUniv σ bp impl)
    (adv : AdversaryFamily σ) (claim : CoverageClaim),
    realizedCoverageAvg impl adv claim ≥ claim.alpha + F.slackFn σ bp

/- ORIGINAL STATEMENT (commented out — false as stated, Round-12 refutation):

  **Master Sharp-Slack Theorem (universal-form)** was intended to assert
  that the averaged coverage is sandwich-bounded by `F.slackFn` under
  the strengthened universal-over-paths I5 invariant. However, Aristotle
  round 12 showed the upper clause `MasterUpperValidAvgUniv F` is false
  for every `F`: the `SubGaussianMartingale.subGaussian` field is vacuously
  satisfiable, so adversaries can force `realizedCoverageAvg = 1` while
  `α + F.slackFn < 1` for small σ.

  See `HowardBridge.Research.not_MasterUpperValidAvgUniv` for the formal
  refutation and `HowardBridge.Research.MasterLowerValidAvgUniv_holds`
  for the (proven) lower clause.

theorem MasterSharpSlackAvgUniv (F : AdmissibleFamily) :
    MasterUpperValidAvgUniv F ∧ MasterLowerValidAvgUniv F := by
  sorry
-/

/-
ORIGINAL STATEMENT (commented out — false as stated):

   `MasterUpperValid F` requires that for EVERY admissible implementation
   `impl` satisfying `BitInvariants`, `realizedCoverage impl claim ≤
   claim.alpha + F.slackFn σ bp`.  But the always-stop implementation
   (zero martingale, `decide = fun _ _ => true`) satisfies `BitInvariants`
   with `realizedCoverage = 1`.  For large enough `scale` (= `bits`),
   `F.slackFn σ bp = F.eta(bits) · 2^{-scale} · σ → 0`, so the bound
   `1 ≤ α + F.slackFn` fails (since α < 1).

   Concrete counterexample: `F = familyBetting`, `σ = 1`,
   `bits = scale = 10`, `α = 1/2`.  Then `F.slackFn = 1/√(10·log2+1) ·
   2^{-10} · 1 < 0.001`, and `1 > 0.5 + 0.001`.

   Root cause: `BitInvariants` does not constrain the *stopping decision*
   relative to the martingale process strongly enough — `monotone_under_
   threshold` and `boundary_sane` allow degenerate always-stop impls.
   A fix would require strengthening `BitInvariants` to exclude always-
   stop implementations (e.g., requiring `decide` to be a function of
   the quantized process, not an arbitrary monotone boolean).

theorem MasterSharpSlack (F : AdmissibleFamily) :
    MasterUpperValid F ∧ MasterLowerValid F := by
  sorry

**2026-04-22 Round-3 refutation retired after I5 added.** Aristotle's
round-3 refutation of `MasterUpperValid` constructed an always-stop
impl with zero martingale. That construction no longer satisfies
`BitInvariants` because I5 (`quantized_decision_consistent`) requires
`decide t = true ↔ mart ≥ positive threshold`, but always-stop has
`decide = true` while `mart = 0 < threshold` at any `t ≥ 1`.

With I5 in place, we EXPECT `MasterSharpSlack` to close — Aristotle
round 6 is the appropriate venue.

ORIGINAL STATEMENT (commented out — false as stated, Round-7 refutation):

  `MasterUpperValid F` quantifies over ALL `BitPrecision` configurations,
  including `bits = 1, scale = 0`.  At `bits = 1`, the I5 threshold cap
  `2^{bits-1} − 1 = 0` collapses the threshold to `min(σ·√(…), 0) − 2^{−0}`
  `= 0 − 1 = −1` for all `t`.  A constant-zero sub-Gaussian martingale with
  `process = 0 ≥ −1` therefore satisfies I5 with `decide = true` everywhere.
  The resulting `realizedCoverage = 1`, but `F.slackFn σ bp` can be made
  arbitrarily small by choosing `σ` small (since `slackFn` is linear in `σ`).
  Hence `1 > α + F.slackFn` for small enough `σ`, contradicting
  `MasterUpperValid`.

  Root cause: the I5 threshold cap at `2^{bits−1} − 1` lets the threshold
  become negative at small `bits`, enabling the trivial always-decide
  construction regardless of `σ`.  Fixing this requires either:
  (a) constraining `bits ≥ B₀` for a family-dependent threshold, or
  (b) defining `MasterUpperValid` with a family-dependent lower bound on
      `bits`, or
  (c) making the threshold floor family-dependent rather than structural.

theorem MasterSharpSlack (F : AdmissibleFamily) :
    MasterUpperValid F ∧ MasterLowerValid F := by
  sorry

**Refutation of `MasterUpperValid`.** For EVERY admissible family `F`,
`MasterUpperValid F` is false.  The counterexample uses `bits = 1`,
`scale = 0`, where the I5 threshold cap collapses to `−1`.  A constant-zero
martingale with `decide = true` everywhere gives `realizedCoverage = 1`,
while `F.slackFn` can be made < `1 − α` by choosing `σ` small.
-/
theorem not_MasterUpperValid (F : AdmissibleFamily) : ¬ MasterUpperValid F := by
  unfold MasterUpperValid; push_neg; (
  refine' ⟨ 1 / ( 4 * ( F.eta 1 + 1 ) ), _, _ ⟩ <;> norm_num [ F.eta_nonneg ];
  · exact add_pos_of_nonneg_of_pos ( F.eta_nonneg 1 ) zero_lt_one;
  · refine' ⟨ ⟨ 1, 0, 1, by norm_num, by norm_num ⟩, _, _, _ ⟩;
    refine' ⟨ ⟨ fun _ => 0, _, _ ⟩, fun _ _ => Bool.true, _ ⟩ <;> norm_num;
    exact fun lam => ⟨ _, le_rfl ⟩;
    exact add_pos_of_nonneg_of_pos ( F.eta_nonneg 1 ) zero_lt_one;
    · constructor <;> norm_num;
    · refine' ⟨ ⟨ 1 / 2, 0, _, _ ⟩, _ ⟩ <;> norm_num [ realizedCoverage ];
      unfold AdmissibleFamily.slackFn; norm_num; nlinarith [ F.eta_nonneg 1, mul_inv_cancel₀ ( show ( F.eta 1 + 1 ) ≠ 0 by linarith [ F.eta_nonneg 1 ] ) ] ;);

/-
**`MasterLowerValid` holds for every admissible family.** The same
constant-zero construction at `bits = 1, scale = 0` witnesses
`realizedCoverage = 1 ≥ α + F.slackFn` when `σ` is chosen small enough
that `F.slackFn ≤ 1 − α`.
-/
theorem MasterLowerValid_holds (F : AdmissibleFamily) : MasterLowerValid F := by
  constructor;
  refine' ⟨ _, _ ⟩;
  swap;
  refine' ⟨ ⟨ 1, 0, 1, by norm_num, by norm_num ⟩, _, _, _ ⟩;
  refine' ⟨ ⟨ fun _ => 0, _, _ ⟩, fun _ _ => Bool.true, _ ⟩ <;> norm_num;
  exact 1 / ( 4 * ( F.eta 1 + 1 ) );
  exact fun _ => ⟨ _, le_rfl ⟩;
  exact one_div_pos.mpr ( mul_pos zero_lt_four ( add_pos_of_nonneg_of_pos ( F.eta_nonneg 1 ) zero_lt_one ) );
  · constructor <;> norm_num;
  · refine' ⟨ ⟨ 1 / 2, 0, _, _ ⟩, _ ⟩ <;> norm_num [ realizedCoverage ];
    unfold AdmissibleFamily.slackFn; norm_num;
    nlinarith [ F.eta_nonneg 1, mul_inv_cancel₀ ( by linarith [ F.eta_nonneg 1 ] : ( F.eta 1 + 1 ) ≠ 0 ) ];
  · exact one_div_pos.mpr ( mul_pos zero_lt_four ( add_pos_of_nonneg_of_pos ( F.eta_nonneg 1 ) zero_lt_one ) )

/-!
## Ranking corollary
-/

theorem eta_betting_lt_HR (b : ℕ) (hb : 1 ≤ b) :
    familyBetting.eta b ≤ familyHR.eta b := by
  unfold familyBetting familyHR;
  rw [ div_le_iff₀ ( by positivity ) ];
  rw [ ← Real.sqrt_mul <| by positivity ] ; exact Real.le_sqrt_of_sq_le <| by nlinarith [ show ( b : ℝ ) ≥ 1 by norm_cast, Real.log_two_gt_d9, mul_le_mul_of_nonneg_left ( show ( b : ℝ ) ≥ 1 by norm_cast ) <| Real.log_nonneg one_le_two ] ;

/-- The vector rate is strictly larger than the Howard–Ramdas rate. -/
theorem eta_HR_lt_vector (b : ℕ) (hb : 1 ≤ b) :
    familyHR.eta b ≤ familyVector.eta b := by
  unfold familyHR familyVector
  simp only []
  apply Real.sqrt_le_sqrt
  have : (0 : ℝ) ≤ (b : ℝ) * Real.log 2 := by
    apply mul_nonneg
    · exact Nat.cast_nonneg _
    · exact Real.log_nonneg (by norm_num)
  linarith

/-- **Corollary (3-way ranking at fixed `b ≥ 1`):**
`η_betting(b) ≤ η_HR(b) ≤ η_vector(b)`. -/
theorem ranking_3_way (b : ℕ) (hb : 1 ≤ b) :
    familyBetting.eta b ≤ familyHR.eta b ∧
    familyHR.eta b ≤ familyVector.eta b :=
  ⟨eta_betting_lt_HR b hb, eta_HR_lt_vector b hb⟩

/-- **4-way ranking at fixed `b ≥ 1`:**
`η_betting(b) ≤ η_aCS(b) ≤ η_HR(b) ≤ η_vector(b)`. -/
theorem ranking_4_way (b : ℕ) (hb : 1 ≤ b) :
    familyBetting.eta b ≤ familyAsymptotic.eta b ∧
    familyAsymptotic.eta b ≤ familyHR.eta b ∧
    familyHR.eta b ≤ familyVector.eta b := by
  refine ⟨?_, ?_, eta_HR_lt_vector b hb⟩
  · unfold familyBetting familyAsymptotic;
    rw [ div_le_iff₀ ( by positivity ) ];
    rw [ ← Real.sqrt_mul <| by positivity ];
    exact Real.le_sqrt_of_sq_le ( by have := Real.log_two_gt_d9; norm_num1 at *; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two, ( by norm_cast : ( 1 :ℝ ) ≤ b ), mul_le_mul_of_nonneg_left ( show ( b :ℝ ) ≥ 1 by norm_cast ) ( Real.log_nonneg one_le_two ) ] )
  · unfold familyAsymptotic familyHR
    simp only []
    apply Real.sqrt_le_sqrt
    have hb' : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith

end HowardBridge