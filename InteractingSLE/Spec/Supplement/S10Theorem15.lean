/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S10Main

/-!
# Supplement §10 for the original flows: W8's later selection and the Theorem 1.5 inputs

Packet PROVE-SUPP10 (specification supplement §10, `source/spec/p529-576.md`, pp. 538–544).

* **Ordered seeds, non-crossing sector** (`ae_contactsIncreasing_of_lt`): for flow lines from `x₂ < x₁` with
  `θ₁ < θ₂`, W6's argument with Aux. lemma 84 (the distinct-seed boundary order) in place of G5 makes all contacts
  increasing, finite thresholds included.
* **Theorem W8, common later selection and no return** (`W8LaterSelectionStatement`, pp. 538–540) for the original
  flows from `x₂ < x₁`, `θ₁ < θ₂ + π`, every start `σ`: proved from increasing contact order of the original flows
  (`w8LaterSelectionStatement_of_contactsIncreasing`). That order is proved here in the sector `θ₁ < θ₂`
  (`originalContactsIncreasing_of_lt`), so W8's selection holds there from W5, W2a, Aux. 84 and Aux. 25
  (`w8LaterSelection_of_lt`). For `θ₂ ≤ θ₁ < θ₂ + π` the source obtains it from W6 for the conditional common-seed
  pair in the first-contact chart, transported by W7; that conditional step is the named proposition
  `OriginalContactsIncreasingStatement`.
* **The Theorem 1.5 inputs** (`Theorem15Inputs.lean`), each from Lemma 7.7, Aux. 25 and one named chart-level
  proposition, the conditional step of its source proof:
  - `criticalExclusionAfterCrossingStatement_of_inputs` with `ChartInteriorExclusionStatement`;
  - `thm712CMergingStatement_of_inputs` with `CommonFlowAfterFirstContactStatement`;
  - `thm712CCrossingStatement_of_inputs` with `ChartOrderAfterCrossingStatement`.
  The §10 step proved for the critical exclusion: "First-contact confinement and no return put every subsequent
  common point of the original open domain in the interior of this chart" (`mem_activeDomain_of_notMem`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp10

open Sec7 Theorem15

/-! ### Ordered seeds in the non-crossing sector -/

/-- **Increasing contacts for ordered distinct seeds** (W6's argument, with Aux. lemma 84 for the strict contacts):
for flow lines from `x₂ < x₁` with `θ₁ < θ₂`, almost surely all finite-parameter contacts, finite thresholds
included, are increasing. -/
theorem ae_contactsIncreasing_of_lt (hW5 : W5Statement.{u}) (hW2a : W2aStatement.{u})
    (h84 : Aux84Statement) (hA25 : Aux25Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ}
    (hx : x₂ < x₁) (hθ : θ₁ < θ₂) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (h₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (h₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) := by
  have e5 := hW5 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx.le hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  have e2a := hW2a κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx.le hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [e5, e2a, ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁, ae_apply_zero_of_isFlowLine h₁,
    ae_apply_zero_of_isFlowLine h₂] with ω hord hfr hi₁ h0₁ h0₂
  refine contactsIncreasing_of_strict_of_frontier hi₁ ?_ ?_
  · intro s s' t t' hs hs' ht ht' hst hst' hlt
    exact contacts_strict_increasing_of_completions_of_lt h84 hx h0₁ h0₂ hord hs hs' ht ht' hst hst' hlt
  · intro A B hA hB
    exact hfr A B hA hB fun a c ha hc =>
      hord a c ((ENNReal.coe_lt_coe.mpr ha).trans_le hA) ((ENNReal.coe_lt_coe.mpr hc).trans_le hB)

/-! ### Theorem W8 for the original flows -/

/-- **Theorem W8, common later selection and no return** (general finite-word later-contact restart; supplement
§10, pp. 538–540; Theorem 7.9B, p. 459), its geometric selection assertions: for flow lines from `x₂ < x₁` with
`θ₁ < θ₂ + π` and every start `σ` of the second path, "the two finite-parameter first contact selections between the
full first prefix and the second suffix starting at `σ` are either both absent, or are attained at the same physical
point" (a coordinatewise least later contact `p`), and "after their common initial point the available tails avoid
the selected old union" `η₁([0, p.1]) ∪ η₂([0, p.2])` (in particular the second prefix before `σ`). The start `σ` is
arbitrary (the source takes an own-filtration stop), so this is a pathwise statement for all `σ` at once. -/
def W8LaterSelectionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ σ : ℝ≥0∞, (laterContactSet (η₁ ω) (ζ₁ ω) (η₂ ω) σ (ζ₂ ω)).Nonempty →
        ∃ p ∈ laterContactSet (η₁ ω) (ζ₁ ω) (η₂ ω) σ (ζ₂ ω),
          (∀ q ∈ laterContactSet (η₁ ω) (ζ₁ ω) (η₂ ω) σ (ζ₂ ω), p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∧
          (∀ s : ℝ≥0, p.1 < s → (s : ℝ≥0∞) ≤ ζ₁ ω →
            η₁ ω s ∉ η₁ ω '' Icc 0 p.1 ∪ η₂ ω '' Icc 0 p.2) ∧
          ∀ t : ℝ≥0, p.2 < t → (t : ℝ≥0∞) ≤ ζ₂ ω →
            η₂ ω t ∉ η₁ ω '' Icc 0 p.1 ∪ η₂ ω '' Icc 0 p.2

/-- **Remaining proposition for W8 (conditional step): increasing contact order of the original flows** from
`x₂ < x₁` with `θ₁ < θ₂ + π`. The source proves it (W8, pp. 539–540) by applying W6 to the canonical common-seed pair
of the first-contact conditional field (Lemma 7.8, the conditional continuation kernels), and W7's identification of
the original later contact relation with that of the canonical pair ("W7 says that the original later contact
relation is exactly …"). In the sector `θ₁ < θ₂` it is proved without the restart
(`originalContactsIncreasing_of_lt`). -/
def OriginalContactsIncreasingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω)

/-- **Theorem W8, selection** from increasing contact order of the original flows and Aux. 25 (W8's "Common
selection, no return" paragraph, p. 540, applied pathwise). -/
theorem w8LaterSelectionStatement_of_contactsIncreasing (hA25 : Aux25Statement.{u})
    (hinc : OriginalContactsIncreasingStatement.{u}) : W8LaterSelectionStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [hinc κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁, ae_injOn_of_isFlowLine hA25 hκ hκ4 h₂,
    ae_continuousOn_of_isFlowLine h₁, ae_continuousOn_of_isFlowLine h₂] with ω hi hi₁ hi₂ hc₁ hc₂
  exact fun σ hne => w8_selection_of_contactsIncreasing hc₁ hc₂ hi₁ hi₂ hi σ hne

/-- **Theorem W8, selection, in the sector `θ₁ < θ₂`**, for every start `σ`, from W5, W2a, Aux. 84 and Aux. 25
(without the first-contact restart). -/
theorem w8LaterSelection_of_lt (hW5 : W5Statement.{u}) (hW2a : W2aStatement.{u})
    (h84 : Aux84Statement) (hA25 : Aux25Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ}
    (hx : x₂ < x₁) (hθ : θ₁ < θ₂) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (h₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (h₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ σ : ℝ≥0∞, (laterContactSet (η₁ ω) (ζ₁ ω) (η₂ ω) σ (ζ₂ ω)).Nonempty →
      ∃ p ∈ laterContactSet (η₁ ω) (ζ₁ ω) (η₂ ω) σ (ζ₂ ω),
        (∀ q ∈ laterContactSet (η₁ ω) (ζ₁ ω) (η₂ ω) σ (ζ₂ ω), p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∧
        (∀ s : ℝ≥0, p.1 < s → (s : ℝ≥0∞) ≤ ζ₁ ω →
          η₁ ω s ∉ η₁ ω '' Icc 0 p.1 ∪ η₂ ω '' Icc 0 p.2) ∧
        ∀ t : ℝ≥0, p.2 < t → (t : ℝ≥0∞) ≤ ζ₂ ω →
          η₂ ω t ∉ η₁ ω '' Icc 0 p.1 ∪ η₂ ω '' Icc 0 p.2 := by
  filter_upwards [ae_contactsIncreasing_of_lt hW5 hW2a h84 hA25 hκ hκ4 hb hx hθ hh h₁ h₂,
    ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁, ae_injOn_of_isFlowLine hA25 hκ hκ4 h₂,
    ae_continuousOn_of_isFlowLine h₁, ae_continuousOn_of_isFlowLine h₂] with ω hi hi₁ hi₂ hc₁ hc₂
  exact fun σ hne => w8_selection_of_contactsIncreasing hc₁ hc₂ hi₁ hi₂ hi σ hne

/-- In the sector `θ₁ < θ₂`, the remaining proposition holds: increasing contact order of the original flows, from
W5, W2a, Aux. 84 and Aux. 25. -/
theorem originalContactsIncreasing_of_lt (hW5 : W5Statement.{u}) (hW2a : W2aStatement.{u})
    (h84 : Aux84Statement) (hA25 : Aux25Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ}
    (hx : x₂ < x₁) (hθ : θ₁ < θ₂) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (h₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (h₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ContactsIncreasing (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) :=
  ae_contactsIncreasing_of_lt hW5 hW2a h84 hA25 hκ hκ4 hb hx hθ hh h₁ h₂

/-! ### The interior of the first-contact chart -/

/-- In an open set `U ⊆ ℂ`, a point of `U` in the closure of the unbounded part of `U` lies in the unbounded part:
its component is open, so it meets an unbounded component, which is then its own. -/
theorem mem_unboundedPart_of_mem_closure {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U)
    (hcl : z ∈ closure (unboundedPart U)) : z ∈ unboundedPart U := by
  obtain ⟨w, hwC, hwU⟩ := mem_closure_iff.mp hcl _ hU.connectedComponentIn
    (mem_connectedComponentIn hz)
  exact ⟨hz, fun hb => hwU.2 (by rwa [← connectedComponentIn_eq hwC])⟩

/-- **Critical exclusion after a crossing, the physical transfer** (supplement p. 544: "First-contact confinement and
no return put every subsequent common point of the original open domain in the interior of this chart"): a point of
`ℍ` off the two first-contact prefixes `K = η₁([0, s₀]) ∪ η₂([0, t₀])` and in the closure of the active domain
(confinement) lies in the active domain itself, the domain of the chart. -/
theorem mem_activeDomain_of_notMem {η₁ η₂ : ℝ≥0 → ℂ} {s₀ t₀ : ℝ≥0}
    (hc₁ : ContinuousOn η₁ (Icc 0 s₀)) (hc₂ : ContinuousOn η₂ (Icc 0 t₀)) {z : ℂ}
    (hzH : z ∈ QuantumZipper.H) (hzK : z ∉ η₁ '' Icc 0 s₀ ∪ η₂ '' Icc 0 t₀)
    (hcl : z ∈ closure (activeDomain η₁ s₀ η₂ t₀)) : z ∈ activeDomain η₁ s₀ η₂ t₀ := by
  have hK : IsClosed (η₁ '' Icc 0 s₀ ∪ η₂ '' Icc 0 t₀) :=
    ((isCompact_Icc.image_of_continuousOn hc₁).union
      (isCompact_Icc.image_of_continuousOn hc₂)).isClosed
  exact mem_unboundedPart_of_mem_closure (QuantumZipper.isOpen_H.sdiff hK) ⟨hzH, hzK⟩ hcl

/-- The pathwise core of the critical exclusion after a crossing: at the first contact `(s₀, t₀)` of injective
continuous available curves, with Lemma 7.7's confinement and no common point of the two strictly later portions in
the active domain, every common point in `ℍ` is the first-contact point. -/
theorem eq_firstContact_of_chartExclusion {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s₀ t₀ : ℝ≥0}
    (hc₁ : ContinuousOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hc₂ : ContinuousOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (hi₁ : InjOn η₁ {s | (s : ℝ≥0∞) ≤ ζ₁}) (hi₂ : InjOn η₂ {t | (t : ℝ≥0∞) ≤ ζ₂})
    (h₀ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀)
    (hconf : ∀ s : ℝ≥0, s₀ ≤ s → (s : ℝ≥0∞) ≤ ζ₁ → η₁ s ∈ closure (activeDomain η₁ s₀ η₂ t₀))
    (hX : ∀ s t : ℝ≥0, s₀ < s → t₀ < t → (s : ℝ≥0∞) ≤ ζ₁ → (t : ℝ≥0∞) ≤ ζ₂ → η₁ s = η₂ t →
      η₁ s ∉ activeDomain η₁ s₀ η₂ t₀)
    {s t : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ζ₁) (ht : (t : ℝ≥0∞) ≤ ζ₂) (hst : η₁ s = η₂ t)
    (hH : η₁ s ∈ QuantumZipper.H) : η₁ s = η₁ s₀ := by
  obtain ⟨hs₀s, ht₀t⟩ := h₀.2.2.2 s t hs ht hst
  rcases hs₀s.lt_or_eq with hlt | rfl
  · rcases ht₀t.lt_or_eq with htlt | rfl
    · exfalso
      have hIcc₁ : Icc 0 s₀ ⊆ {s | (s : ℝ≥0∞) ≤ ζ₁} := fun u hu =>
        (ENNReal.coe_le_coe.mpr hu.2).trans h₀.1
      have hIcc₂ : Icc 0 t₀ ⊆ {t | (t : ℝ≥0∞) ≤ ζ₂} := fun u hu =>
        (ENNReal.coe_le_coe.mpr hu.2).trans h₀.2.1
      have hK := (IsFirstContact.no_return hi₁ hi₂ h₀).1 s hlt hs
      exact hX s t hlt htlt hs ht hst
        (mem_activeDomain_of_notMem (hc₁.mono hIcc₁) (hc₂.mono hIcc₂) hH hK (hconf s hs₀s hs))
    · rw [hst, ← h₀.2.2.1]
  · rfl

/-! ### Named chart-level propositions (the conditional steps) and the Theorem 1.5 inputs -/

/-- **Remaining proposition for the critical exclusion (conditional step): Theorem 7.12D in the first-contact
chart**, pulled back by the chart. In the setting of `Theorem15.CriticalExclusionAfterCrossingStatement`, on the
meeting branch with two nonempty continuations, the strictly later available portions have no common point in the
active domain `D` of the first-contact prefixes. Source (p. 544): "The actual first-contact conditional paths start
from one common prime end, with their higher-angle first continuation on the left. Apply 7.12D in that conditional
chart. There is no subsequent common interior point." The chart `φ : D → ℍ` is a bijection (`IsActiveChart`), so a
common point of the chart paths in `ℍ` is exactly a common point of the physical paths in `D`. -/
def ChartInteriorExclusionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₂ < θ₁ → θ₁ < θ₂ + Real.pi →
    κ / 2 ≤ (θ₁ - θ₂) * QuantumZipper.chiC κ / sleLambda κ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        ∀ s t : ℝ≥0, s₀ < s → t₀ < t → (s : ℝ≥0∞) ≤ ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → η₁ ω s = η₂ ω t →
          η₁ ω s ∉ activeDomain (η₁ ω) s₀ (η₂ ω) t₀

/-- **The Theorem 1.5 input `CriticalExclusionAfterCrossingStatement`** (supplement p. 544), from Lemma 7.7
(confinement), Aux. 25 (simplicity) and 7.12D in the first-contact chart. -/
theorem criticalExclusionAfterCrossingStatement_of_inputs (h77 : Lemma77Statement.{u})
    (hA25 : Aux25Statement.{u}) (hX : ChartInteriorExclusionStatement.{u}) :
    CriticalExclusionAfterCrossingStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ hcrit Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [h77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx (by linarith) P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    hX κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ hcrit P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    ae_injOn_of_isFlowLine hA25 hκ hκ4 h₁, ae_injOn_of_isFlowLine hA25 hκ hκ4 h₂,
    ae_continuousOn_of_isFlowLine h₁, ae_continuousOn_of_isFlowLine h₂] with
    ω h7 hXω hi₁ hi₂ hc₁ hc₂
  intro s₀ t₀ h₀ hs₀ ht₀ s t hs ht hst hH
  obtain ⟨s₀', t₀', h₀', hconf, -⟩ := h7 ⟨s₀, t₀, h₀.1, h₀.2.1, h₀.2.2.1⟩
  obtain ⟨rfl, rfl⟩ := IsFirstContact.unique h₀' h₀
  exact eq_firstContact_of_chartExclusion hc₁ hc₂ hi₁ hi₂ h₀' hconf (hXω s₀' t₀' h₀' hs₀ ht₀) hs ht hst hH

/-- **Remaining proposition for merging (conditional step): one conditional flow after the first contact.** In the
setting of `Theorem15.Thm712CMergingStatement`, on the meeting branch with two nonempty continuations, both available
continuations are one path `Γ` read through strictly increasing clocks `cᵢ` mapping relative available intervals
`[0, Uᵢ]` onto `[s₀, ζ₁]`, `[t₀, ζ₂]`. Source (p. 542): "both conditional paths have the same field, initial finite
word and angle. Universal finite-force determination gives one canonical path function. The two actual futures are
that same path stopped at their respective reconstructed own stopping times" (`Γ = φ⁻¹ ∘ γ`, `cᵢ` the capacity
clocks (W8.1); Corollary 7.12E, p. 461). -/
def CommonFlowAfterFirstContactStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ : ℝ, x₂ < x₁ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        ∃ (Γ : ℝ≥0 → ℂ) (U₁ U₂ : ℝ≥0∞) (c₁ c₂ : ℝ≥0 → ℝ≥0),
          StrictMonoOn c₁ {u | (u : ℝ≥0∞) ≤ U₁} ∧ StrictMonoOn c₂ {u | (u : ℝ≥0∞) ≤ U₂} ∧
          c₁ '' {u | (u : ℝ≥0∞) ≤ U₁} = {s | s₀ ≤ s ∧ (s : ℝ≥0∞) ≤ ζ₁ ω} ∧
          c₂ '' {u | (u : ℝ≥0∞) ≤ U₂} = {t | t₀ ≤ t ∧ (t : ℝ≥0∞) ≤ ζ₂ ω} ∧
          (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₁ → η₁ ω (c₁ u) = Γ u) ∧
          ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ U₂ → η₂ ω (c₂ u) = Γ u

/-- **The Theorem 1.5 input `Thm712CMergingStatement`** (Theorem 7.12C, equal angles, p. 542), from one conditional
flow after the first contact: "Mapping back through `φ⁻¹` gives the claimed merging and prevents any later separation
while both are available" (`Sec7.agreeAsCurvesAfter_of_clocks`). -/
theorem thm712CMergingStatement_of_inputs (hC : CommonFlowAfterFirstContactStatement.{u}) :
    Thm712CMergingStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ hx Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [hC κ hκ hκ4 b jumps hb x₁ x₂ θ hx P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂] with ω hω
  intro s₀ t₀ h₀ hs₀ ht₀
  obtain ⟨Γ, U₁, U₂, c₁, c₂, hm₁, hm₂, him₁, him₂, he₁, he₂⟩ := hω s₀ t₀ h₀ hs₀ ht₀
  exact agreeAsCurvesAfter_of_clocks hm₁ hm₂ him₁ him₂ he₁ he₂

/-- **Remaining proposition for crossing (conditional step): W5 in the first-contact chart.** In the setting of
`Theorem15.Thm712CCrossingStatement`, on the meeting branch with two nonempty continuations, there is a common active
chart `φ` of the active domain `D` centered at the contact point, the available continuations have chart images
`γ₁`, `γ₂` (limits of `φ` within `D`), and every pair of strict finite outgoing prefixes has ordered proper
completions with `γ₁` on the left. Source (p. 542): "In the strict-angle case, apply W5 to that same field, with the
angles listed in increasing order. It puts the higher-angle first path to the left of the lower-angle second path for
every pair of strict finite outgoing prefixes." -/
def ChartOrderAfterCrossingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ < x₁ → θ₂ < θ₁ → θ₁ < θ₂ + Real.pi →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
        (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω →
        ∃ φ : ℂ → ℂ, IsActiveChart (activeDomain (η₁ ω) s₀ (η₂ ω) t₀) (η₁ ω s₀) φ ∧
          ∃ γ₁ γ₂ : ℝ≥0 → ℂ,
            (∀ u : ℝ≥0, ((s₀ + u : ℝ≥0) : ℝ≥0∞) < ζ₁ ω →
              Tendsto φ (𝓝[activeDomain (η₁ ω) s₀ (η₂ ω) t₀] (η₁ ω (s₀ + u))) (𝓝 (γ₁ u))) ∧
            (∀ v : ℝ≥0, ((t₀ + v : ℝ≥0) : ℝ≥0∞) < ζ₂ ω →
              Tendsto φ (𝓝[activeDomain (η₁ ω) s₀ (η₂ ω) t₀] (η₂ ω (t₀ + v))) (𝓝 (γ₂ v))) ∧
            ∀ u v : ℝ≥0, ((s₀ + u : ℝ≥0) : ℝ≥0∞) < ζ₁ ω → ((t₀ + v : ℝ≥0) : ℝ≥0∞) < ζ₂ ω →
              HasOrderedProperCompletions γ₂ v γ₁ u

/-- **The Theorem 1.5 input `Thm712CCrossingStatement`** (Theorem 7.12C, strict angles, p. 542), from Lemma 7.7's
confinement ("the range of `ηᵢ|[τᵢ, Tᵢ]` is contained in the closure of the unbounded connected component") and W5
in the first-contact chart. -/
theorem thm712CCrossingStatement_of_inputs (h77 : Lemma77Statement.{u})
    (hO : ChartOrderAfterCrossingStatement.{u}) : Thm712CCrossingStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂
  filter_upwards [h77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂,
    hO κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ P h hh η₁ η₂ ζ₁ ζ₂ h₁ h₂] with ω h7 hOω
  intro s₀ t₀ h₀ hs₀ ht₀
  obtain ⟨s₀', t₀', h₀', hconf₁, hconf₂⟩ := h7 ⟨s₀, t₀, h₀.1, h₀.2.1, h₀.2.2.1⟩
  obtain ⟨rfl, rfl⟩ := IsFirstContact.unique h₀' h₀
  obtain ⟨φ, hφ, γ₁, γ₂, hγ₁, hγ₂, hord⟩ := hOω s₀' t₀' h₀' hs₀ ht₀
  refine ⟨φ, hφ, γ₁, γ₂, fun u hu => ⟨hconf₁ _ le_self_add hu.le, hγ₁ u hu⟩,
    fun v hv => ⟨hconf₂ _ le_self_add hv.le, hγ₂ v hv⟩, hord⟩

end Supp10

end InteractingSLE
