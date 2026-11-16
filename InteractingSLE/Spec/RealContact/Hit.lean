/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.Statements
import InteractingSLE.Spec.RealContact.HitReal
import InteractingSLE.Spec.AuditFix.BoundaryContact
import InteractingSLE.Spec.Supplement.G7Measurable
import InteractingSLE.Spec.Supplement.G7RetainedReduce
import InteractingSLE.Spec.Supplement.S10Weights
import InteractingSLE.Spec.Supplement.S9BOrder
import InteractingSLE.Spec.Theorem15D5Critical
import InteractingSLE.Frozen.Spec.IsFlowLine_stays_right_of_lt

/-!
# The real first-hit exclusion is equivalent to the pocket-corner exclusion

Packet PROVE-RC-HIT (ruling R124 (a)). **The packet's target `RealContact.G7GB7aFirstHitRealStatement` is not proved
here.** This file shows that it is *equivalent* to one statement that no landed input covers,
`PocketCornerStatement`, and proves both directions with closed inputs only.

## The pocket corner

Setting of `G7GB7aFirstHitRealStatement` (`η₁` lower angle from `x₁`, `η₂` higher angle from `x₂ ≤ x₁`, (7.12D.1)).
`PocketCornerStatement`: almost surely the second path does not end (`T = ζ₂`) at a real point `q < x₂` which the
first path visits strictly before its lifetime (`η₁ x = q`, `x < ζ₁`).

Geometry. When `η₁` touches `ℝ` at `q < x₂` at time `x < ζ₁`, the arc `η₁([0, x])` and `[q, x₁]` bound a pocket which
contains the second seed. By W5 and the interior exclusion, `η₂` stays in the closure of this pocket, so for every
first cutoff `u > x` the second tip is in a bounded component of `ℍ \ η₁([0, u])`: it is never adherent to the joint
unbounded component, there is no ordinary retained pair (`Supp7.IsOrdinaryRetainedPair`), and Lemma G7's kernel
(`Supp7.G7RetainedPairStatement`) never applies. For cutoffs `u < x` the corner `q` is a point of the untouched real
line in the retained chart, determined by the future of `η₁`, not by the retained data. In the original domain `q` is
random, so G12 for fixed points does not apply either. The left weight of `η₂` near `q` is `< −2`, so `η₂` can end on
that real interval. The configuration is consistent with W5's ordered completions: the completion of the `η₂` prefix
leaves the pocket along the `η₁` arc. It is the left-hand case of the specification's Lemma G15 (p. 508), which treats
it as a possible configuration for general angles.

The statement is expected to hold, by an argument that is not formalized. Conditionally on `η₁` stopped at its first
hit of `(−∞, x₂)`, the second path is the angle-`θ₂` flow line of the conditional field in the pocket. In a chart of
the pocket sending `x₂ ↦ 0` and the corner `q ↦ ∞`, its left boundary near `∞` carries cumulative weight `< −2`, so it
reaches its continuation threshold at a finite chart point, not at `q`. The project has no conditional law of a flow
line inside a bounded pocket of another flow line, so this is a genuinely missing input (handoff
`planning/handoffs/PROVE-RC-HIT.md`).

## Main results

* `PocketCornerStatement` (the missing input; **not proved in Lean**);
* **`g7GB7aFirstHitReal_of_pocketCorner`**: `PocketCornerStatement → G7GB7aFirstHitRealStatement`. Interior hits are
  excluded by the sealed critical interior clause (`AuditFix.criticalOrderedNoInteriorPoint_holds`). Real hits are
  pocket corners (`Hit.ae_realContact_cases`, closed).
* **`pocketCorner_of_g7GB7aFirstHitReal`**: the converse. At a pocket corner choose `u ∈ (x, ζ₁)` and `r = T/2`.
  `Hit.ae_realContact_cases` and the interior clause show that `η₂` meets `η₁([0, u])` at no time in `(0, T)`.
  W5 (the frozen `IsFlowLine.stays_right_of_lt`) and the strict contact order
  (`Theorem15D5.ae_strictContactsIncreasing`) supply the remaining hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.RealContact

/-- **The pocket-corner exclusion** (the missing input of PROVE-RC-HIT; **not proved in Lean**). In the setting of
`G7GB7aFirstHitRealStatement`, almost surely there are no `x < ζ₁` and `T = ζ₂` (finite) with
`η₁ x = η₂ T = q` for a real `q < x₂`. Equivalently (`Hit.ae_realContact_cases`): the higher-angle path does not end
at a strictly available real point of the lower-angle path. See the module docstring for why no landed input gives
it, and for its mathematical proof (the conditional law of `η₂` in the pocket of `η₁` closed at `q`). -/
def PocketCornerStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ →
    κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ (x T : ℝ≥0) (q : ℝ), (x : ℝ≥0∞) < ζ₁ ω → (T : ℝ≥0∞) = ζ₂ ω → q < x₂ →
        η₁ ω x = q → η₂ ω T = q → False

namespace Hit

/-- (7.12D.1) gives the frozen critical-angle hypothesis `πκ/(4 − κ) ≤ θ₂ − θ₁`. -/
theorem critical_of_weight {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hD : κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ)) :
    Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁ :=
  (Theorem15.half_le_mul_chiC_div_sleLambda_iff hκ hκ4 _).1 ((Supp10.thm712D_one hκ θ₁ θ₂).1 hD)

/-- **Every contact of the live first path at a positive second time is a pocket corner, almost surely** (closed):
interior contacts do not occur (the sealed critical interior clause), and real ones have `t = ζ₂` and `q < x₂`
(`ae_realContact_cases`). -/
theorem ae_contact_cases {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁)
    (hD : κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ))
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ x t : ℝ≥0, (x : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → 0 < t → η₁ ω x = η₂ ω t →
      η₁ ω x = ((η₁ ω x).re : ℂ) ∧ (t : ℝ≥0∞) = ζ₂ ω ∧ (η₁ ω x).re < x₂ := by
  have hθ := Supp7.lt_of_weight hκ hκ4 hD
  filter_upwards [AuditFix.criticalOrderedNoInteriorPoint_holds hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂
      (critical_of_weight hκ hκ4 hD),
    ae_realContact_cases hκ hκ4 hb hx hD hh hη₁ hη₂, Supp7.ae_im_nonneg_of_isFlowLine hη₁]
    with ω hI hR hIm
  intro x t hxζ htζ ht0 heq
  have hnotH : η₁ ω x ∉ QuantumZipper.H := hI x t hxζ.le htζ heq
  have him : (η₁ ω x).im = 0 := le_antisymm (not_lt.1 hnotH) (hIm x hxζ.le)
  have h₁ : η₁ ω x = ((η₁ ω x).re : ℂ) := Complex.ext (by simp) (by simp [him])
  obtain ⟨hT, hq⟩ := hR x t (η₁ ω x).re hxζ htζ ht0 h₁ (heq.symm.trans h₁)
  exact ⟨h₁, hT, hq⟩

end Hit

open Hit

/-- **The real first-hit exclusion from the pocket-corner exclusion.** A proposed first new hit `η₂ t = η₁ x`,
`x < u < ζ₁`, `r < t ≤ ζ₂`, is a pocket corner (`Hit.ae_contact_cases`), which `PocketCornerStatement` excludes. -/
theorem g7GB7aFirstHitReal_of_pocketCorner (hP : PocketCornerStatement.{u}) :
    G7GB7aFirstHitRealStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [ae_contact_cases hκ hκ4 hb hx hD hh hη₁ hη₂,
    hP κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂] with ω hC hPω
  intro _ _ u r hu _ _ t x hrt ht hxu heq _
  have hxζ : (x : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_lt_coe.2 hxu).trans hu
  obtain ⟨h₁, hT, hq⟩ := hC x t hxζ ht (lt_of_le_of_lt zero_le hrt) heq.symm
  exact hPω x t _ hxζ hT hq h₁ (heq.trans h₁)

/-- **The pocket-corner exclusion from the real first-hit exclusion** (the converse): the packet's target is exactly
as strong as `PocketCornerStatement`. -/
theorem pocketCorner_of_g7GB7aFirstHitReal (hR : G7GB7aFirstHitRealStatement.{u}) :
    PocketCornerStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  have hθ := Supp7.lt_of_weight hκ hκ4 hD
  have hW5 : Theorem15.W5Statement.{u} := by
    intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
    exact (IsFlowLine.stays_right_of_lt hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂).1
  filter_upwards [hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    (IsFlowLine.stays_right_of_lt hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂).1,
    Theorem15D5.ae_strictContactsIncreasing hW5 Supp9B.aux84Statement Supp9B.g5Statement hκ hκ4 hb hx hθ hh
      hη₁ hη₂,
    ae_contact_cases hκ hκ4 hb hx hD hh hη₁ hη₂, Supp10.ae_apply_zero_of_isFlowLine hη₂]
    with ω hRω hWω hSω hCω h0₂
  intro x T q hxζ hT hq h₁ h₂
  -- the terminal time is positive (the second path starts at `x₂ ≠ q`)
  have hT0 : 0 < T := by
    rcases eq_or_ne T 0 with h0 | h0
    · subst h0
      rw [h0₂] at h₂
      exact absurd (Complex.ofReal_injective h₂) hq.ne'
    · exact pos_iff_ne_zero.2 h0
  obtain ⟨u, hxu, huζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hxζ
  -- no point of the second path at a time in `(0, T)` lies on the first prefix up to `u`
  have hno : ∀ t' : ℝ≥0, 0 < t' → t' < T → η₂ ω t' ∉ η₁ ω '' Icc 0 u := by
    rintro t' ht'0 ht'T ⟨s, hs, he⟩
    have hsζ : (s : ℝ≥0∞) < ζ₁ ω := (ENNReal.coe_le_coe.2 hs.2).trans_lt huζ
    have ht'ζ : (t' : ℝ≥0∞) ≤ ζ₂ ω := by rw [← hT]; exact ENNReal.coe_le_coe.2 ht'T.le
    obtain ⟨-, hT', -⟩ := hCω s t' hsζ ht'ζ ht'0 he
    rw [← hT] at hT'
    exact ht'T.ne (ENNReal.coe_injective hT')
  have hr0 : 0 < T / 2 := half_pos hT0
  have hrT : T / 2 < T := half_lt_self hT0
  have hrζ : ((T / 2 : ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by rw [← hT]; exact ENNReal.coe_lt_coe.2 hrT
  exact hRω hWω hSω u (T / 2) huζ hrζ (hno _ hr0 hrT) T x hrT hT.le (ENNReal.coe_lt_coe.1 hxu)
    (h₂.trans h₁.symm) fun t' h1 h2 => hno t' (hr0.trans h1) h2

end InteractingSLE.RealContact
