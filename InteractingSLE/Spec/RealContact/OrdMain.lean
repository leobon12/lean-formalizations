/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.Statements
import InteractingSLE.Spec.RealContact.OrdLowVisit
import InteractingSLE.Spec.RealContact.OrdCollar
import InteractingSLE.Spec.Theorem15D5Critical
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Supplement.S9BOrder
import InteractingSLE.Spec.Supplement.W0b
import InteractingSLE.Spec.Sec4.Aux25Term
import InteractingSLE.Spec.Sec7.InteractionProbLemma77
import InteractingSLE.Spec.Restart.FCThresholdDriverPremises
import InteractingSLE.Spec.Sec5.Aux61CptThm
import InteractingSLE.Frozen.Spec.IsFlowLine_stays_right_of_lt

/-!
# Theorem 1.5 (i) at critical angles, at every contact, from the real first-hit exclusion

Packet PROVE-RC-ORD (ruling R124 (b)). Main result:

* `criticalOrderedContact_of_firstHitReal : G7GB7aFirstHitRealStatement → CriticalOrderedContactStatement`.

## Route

For W5's ordered pair (`η₁` lower angle from `x₁`, `η₂` higher angle from `x₂ ≤ x₁`, `θ₂ − θ₁ ≥ πκ/(4 − κ)`) and a
contact `η₁ s = η₂ t`, `s ≤ ζ₁`, `t ≤ ζ₂`:

1. **The first path available, `s < ζ₁`** (`ae_firstAvailable`): the contact is the common start.
   * `t > 0`: the two-cutoff collar `false_of_contact_of_firstHitReal` with the real first-hit exclusion `hR` (whose
     weight hypothesis is (7.12D.1), `Theorem15D5.cumWeightRight_exposed_ge_of_half_le`), W5 (the first clause of the
     frozen `IsFlowLine.stays_right_of_lt`), the strict contact order (`Theorem15D5.ae_strictContactsIncreasing`,
     Aux. 84 and G5), W0b (`Supp9.w0bStatement_of_lemma75` in second-arc form) and Aux. 25. The contact may be real
     (in particular at `x₁` when `s = 0`) and `t` may equal `ζ₂`.
   * `t = 0`: `η₁ s = x₂`. If `s = 0` then `x₁ = x₂`, the common start. If `s > 0`: for `x₁ = x₂` injectivity
     (Aux. 25) gives `s = 0`; for `x₂ < x₁` the fixed real point `x₂` is not visited by `η₁` at the available time `s`:
     by Lemma G12 (`Supp7.g12FlowStatement`) when its left cumulative weight for `η₁` exceeds `κ/2 − 4`, and otherwise
     (weight `≤ κ/2 − 4 < −2`) because such a point is visited only at the continuation threshold
     (`OrdLow.ae_ne_of_cumWeightLeft_le`). This covers a degenerate second path (`ζ₂ = 0`), where W0a does not apply.
2. **The first path terminal, `s = ζ₁`, `t < ζ₂`**: the reflection `R(z) = −z̄`
   (`Sec7.FlowReflect.IsFlowLine.reflect`) turns `(η₂, η₁)` into an ordered pair of the reflected field —
   `R ∘ η₂` from `−x₂` at angle `−θ₂` (lower), `R ∘ η₁` from `−x₁ ≤ −x₂` at angle `−θ₁` (higher), the same angle gap
   and lifetimes — in which the contact has the first path available. Step 1 applies.
3. **Both terminal**: the second alternative of the conclusion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace RealContact

open Theorem15D5
open PiecewiseConstantBoundaryData (leftLim)

/-- **Theorem W5, closed at every universe**: the first clause of the sealed frozen Theorem 1.5 (i)
(`IsFlowLine.stays_right_of_lt`). -/
theorem w5Statement_closed : Theorem15.W5Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  exact (IsFlowLine.stays_right_of_lt hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂).1

/-- **Lemma W0b in second-arc form, closed**: `Supp9.w0bStatement_of_lemma75`, with Lemma 7.5 from the proved
Theorems 1.2–1.3 (inline, as in `AuditFix.Cross.w0bStatement_zero_closed`), and Aux. 25. -/
theorem w0bSecondArcStatement_closed : Supp10.W0bSecondArcStatement.{u} :=
  Supp10.w0bSecondArcStatement_of_firstArc
    (Supp9.w0bStatement_of_lemma75 (Restart.FCPlumb.lemma75Statement_of_thm12_thm13
      Sec5.Aux61Cpt.theorem12Statement_of_cptCover Sec5.Aux61Cpt.theorem13Statement_of_cptCover))
    Theorem15.aux25Statement

/-- **The second seed is not visited by the first path at an available time** (`x₂ < x₁`): Lemma G12 when the left
cumulative weight of `x₂` for `η₁` exceeds `κ/2 − 4`, and the threshold lemma `OrdLow.ae_ne_of_cumWeightLeft_le`
otherwise (the weight is then `≤ κ/2 − 4 < −2`). -/
theorem ae_ne_seed_of_lt {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ : Ω → ℝ≥0 → ℂ} {ζ₁ : Ω → ℝ≥0∞} (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) :
    ∀ᵐ ω ∂P, x₂ < x₁ → ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → η₁ ω s ≠ x₂ := by
  by_cases hlt : x₂ < x₁
  · by_cases hS : κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b x₂ + θ₁ * QuantumZipper.chiC κ)
    · filter_upwards [(Supp7.g12FlowStatement κ hκ hκ4 b jumps hb x₁ θ₁ x₂ P h hh η₁ ζ₁ hη₁).2 hlt hS]
        with ω hω _ s hs using hω s hs.le
    · have hS' : Sec4.cumWeightLeft κ (leftLim b x₂ + θ₁ * QuantumZipper.chiC κ) ≤ -2 := by
        linarith [not_lt.1 hS]
      filter_upwards [OrdLow.ae_ne_of_cumWeightLeft_le hκ hb hlt hS' hη₁] with ω hω _ using hω
  · exact Eventually.of_forall fun _ h' => absurd h' hlt

/-- **Step 1: a contact available to the first path is the common start.** For W5's ordered pair at critical angles,
given the real first-hit exclusion: almost surely every contact `η₁ s = η₂ t` with `s < ζ₁` and `t ≤ ζ₂` has
`x₁ = x₂` and `s = t = 0`. -/
theorem ae_firstAvailable (hR : G7GB7aFirstHitRealStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hcrit : Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
      x₁ = x₂ ∧ s = 0 ∧ t = 0 := by
  have hD := (Theorem15.half_le_mul_chiC_div_sleLambda_iff hκ hκ4 (θ₂ - θ₁)).2 hcrit
  have hW := cumWeightRight_exposed_ge_of_half_le hκ hD
  filter_upwards [hR κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hW P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    w5Statement_closed κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    ae_strictContactsIncreasing w5Statement_closed Supp9B.aux84Statement Supp9B.g5Statement hκ hκ4 hb hx hθ hh
      hη₁ hη₂,
    w0bSecondArcStatement_closed κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
    Supp10.ae_apply_zero_of_isFlowLine hη₁, Supp10.ae_apply_zero_of_isFlowLine hη₂,
    ae_ne_seed_of_lt (x₂ := x₂) hκ hκ4 hb hh hη₁]
    with ω hRω hord hCI hW0bω hi₁ hc₁ hc₂ h0₁ h0₂ hseed
  intro s t hs ht hst
  rcases eq_zero_or_pos t with ht0 | ht0
  · -- `t = 0`: `η₁ s = x₂`
    rw [ht0, h0₂] at hst
    rcases eq_zero_or_pos s with hs0 | hs0
    · rw [hs0, h0₁] at hst
      exact ⟨by exact_mod_cast hst, hs0, ht0⟩
    · exfalso
      rcases hx.lt_or_eq with hlt | heq
      · exact hseed hlt s hs hst
      · have h0 : ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ₁ ω := by simp
        exact hs0.ne' (hi₁ hs.le h0 (hst.trans (by rw [h0₁, heq])))
  · -- `t > 0`: the two-cutoff collar with the real first-hit exclusion
    exact absurd (false_of_contact_of_firstHitReal hc₁ hc₂ hi₁ hCI
      (fun a c ha hc => hW0bω a c ha hc (hord a c ha hc)) (hRω hord hCI) hs ht ht0 hst) id

/-- **Theorem 1.5 (i), critical angles, at every contact, from the real first-hit exclusion** (ruling R124 (b)).
`s < ζ₁` is step 1 (`ae_firstAvailable`); `s = ζ₁`, `t < ζ₂` is step 1 for the reflected ordered pair
`(R ∘ η₂, R ∘ η₁)` of the reflected field; `s = ζ₁`, `t = ζ₂` is the second alternative. -/
theorem criticalOrderedContact_of_firstHitReal (hR : G7GB7aFirstHitRealStatement.{u}) :
    CriticalOrderedContactStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hcrit
  have hbR := Sec7.FlowReflect.isPiecewiseConstantBoundaryData_reflData hb
  have hhR := Sec7.FlowReflect.IsGFFWithBoundaryData.reflect hh
  have hη₁R := Sec7.FlowReflect.IsFlowLine.reflect hb hη₁
  have hη₂R := Sec7.FlowReflect.IsFlowLine.reflect hb hη₂
  have hA := ae_firstAvailable hR hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂ hcrit
  have hB := ae_firstAvailable hR hκ hκ4 _ _ hbR (neg_le_neg hx) (neg_lt_neg hθ) hhR hη₂R hη₁R
    (by linarith)
  filter_upwards [hA, hB] with ω hAω hBω
  intro s t hs ht hst
  rcases hs.lt_or_eq with hs' | hs'
  · exact Or.inl (hAω s t hs' ht hst)
  · rcases ht.lt_or_eq with ht' | ht'
    · obtain ⟨hx', ht0, hs0⟩ := hBω t s ht' hs (by rw [hst])
      exact Or.inl ⟨by linarith, hs0, ht0⟩
    · exact Or.inr ⟨hs', ht'⟩

end RealContact

end InteractingSLE
