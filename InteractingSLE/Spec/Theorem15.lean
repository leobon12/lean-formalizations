import InteractingSLE.Spec.Theorem15Inputs
import InteractingSLE.Spec.Sec7.InteractionMerge

/-!
# Theorem 1.5 (constant-angle interaction), assembled from the named inputs

Packet PROVE-SEC7-B2. The three frozen clauses of Theorem 1.5 (Specification p. 5)

* `IsFlowLine.stays_right_of_lt` (i),
* `IsFlowLine.merges` (ii),
* `IsFlowLine.crosses_of_lt` (iii)

are proved here with **exactly their frozen conclusions and binders**, modulo the named inputs of
`Theorem15Inputs.lean` (Theorems W5, W8, 7.12C, 7.12D, the critical exclusion after a crossing, Aux. lemma 25 and
Lemma 7.5), as the specification proves them ("The proof is W5 and 7.12C–7.12D", p. 5; p. 544: "Therefore W5, 7.12C
and 7.12D supply all three interaction clauses of Theorem 1.5"). The theorems carry distinct names
(`…_of_inputs`); they are not providers.

The steps proved here:

* (i): W5 is the first clause; the second clause is 7.12D after the angle conversion
  `D_θ ≥ κ/2 ⟺ θ₂ − θ₁ ≥ πκ/(4 − κ)` (`half_le_mul_chiC_div_sleLambda_iff`) and the remark that an interior available
  contact is a common point of the available ranges in `ℍ`.
* (ii), `x₂ < x₁`: an interior available contact `(s, t)` gives a first contact `(s₀, t₀) ≤ (s, t)` (W8), hence two
  nonempty continuations, so 7.12C merges the curves at `(s₀, t₀)`; merging persists to every later contact of the
  simple curves (`Sec7.agreeAsCurvesAfter_of_isFirstContact`, Corollary 7.12E's last step).
* (ii), `x₂ = x₁`: the two flow lines of the same field with the same seed and angle have the same lifetime and the
  same available path (Lemma 7.5, universal form). A contact `η₁ s = η₂ t = η₁ t` then has `s = t` (Aux. lemma 25),
  and the identity reparametrization merges them (`agreeAsCurvesAfter_self_of_eqOn`).
* (iii), first clause: W8's first contact precedes the interior contact, so both continuations are nonempty and
  7.12C gives the crossing there.
* (iii), second clause: by the critical exclusion after a crossing, an interior available contact has the first
  contact's physical point; simplicity (Aux. lemma 25) turns it into the first contact itself.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem15

open Sec7

/-- Two available paths that coincide on the common available interval `[0, ζ]` agree as curves after any contact
at one common parameter `s ≤ ζ` (the identity reparametrization). -/
theorem agreeAsCurvesAfter_self_of_eqOn {η₁ η₂ : ℝ≥0 → ℂ} {ζ : ℝ≥0∞}
    (heq : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → η₂ t = η₁ t) {s : ℝ≥0} (hs : (s : ℝ≥0∞) ≤ ζ) :
    AgreeAsCurvesAfter η₁ ζ s η₂ ζ s :=
  ⟨ζ, ζ, hs, le_rfl, hs, le_rfl, Or.inl rfl, OrderIso.refl _, fun x => heq x x.2.2⟩

/-- A first contact before an interior available contact leaves both continuations nonempty. -/
theorem IsFirstContact.lt_of_isInteriorAvailableContact {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞}
    {s₀ t₀ s t : ℝ≥0} (h₀ : IsFirstContact η₁ ζ₁ η₂ ζ₂ s₀ t₀)
    (h : IsInteriorAvailableContact η₁ ζ₁ η₂ ζ₂ s t) :
    (s₀ : ℝ≥0∞) < ζ₁ ∧ (t₀ : ℝ≥0∞) < ζ₂ := by
  have hle := Sec7.IsFirstContact.le_of_isInteriorAvailableContact h₀ h
  exact ⟨lt_of_le_of_lt (by exact_mod_cast hle.1) h.1, lt_of_le_of_lt (by exact_mod_cast hle.2) h.2.1⟩

/-- An interior available contact is a contact of the available ranges. -/
theorem IsInteriorAvailableContact.exists_contact {η₁ η₂ : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {s t : ℝ≥0}
    (h : IsInteriorAvailableContact η₁ ζ₁ η₂ ζ₂ s t) :
    ∃ s t : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ∧ (t : ℝ≥0∞) ≤ ζ₂ ∧ η₁ s = η₂ t :=
  ⟨s, t, h.1.le, h.2.1.le, h.2.2.1⟩

/-- **Theorem 1.5 (i)** (Specification p. 5), with exactly the conclusion of the frozen
`IsFlowLine.stays_right_of_lt`, from Theorem W5 (pp. 533–534) and Theorem 7.12D (p. 543). -/
theorem stays_right_of_lt_of_inputs (hW5 : W5Statement.{u}) (h712D : Thm712DStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ ≤ x₁) (hθ : θ₁ < θ₂)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    (∀ᵐ ω ∂P, ∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₂ - θ₁ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        ¬ IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) := by
  refine ⟨hW5 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂, fun hcrit => ?_⟩
  have hD := (half_le_mul_chiC_div_sleLambda_iff hκ hκ4 _).2 hcrit
  filter_upwards [h712D κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hD P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
    with ω hω s t hst
  exact hω s t hst.1.le hst.2.1.le hst.2.2.1 hst.2.2.2

/-- **Theorem 1.5 (ii)** (Specification p. 5), with exactly the conclusion of the frozen `IsFlowLine.merges`,
from Theorem W8 (pp. 538–539), Theorem 7.12C (p. 542), Aux. lemma 25 (p. 127) and Lemma 7.5 (p. 252). -/
theorem merges_of_inputs (hW8 : W8FirstContactStatement.{u}) (hM : Thm712CMergingStatement.{u})
    (hA25 : Aux25Statement.{u}) (hL75 : Lemma75Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ : ℝ} (hx : x₂ ≤ x₁)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
      AgreeAsCurvesAfter (η₁ ω) (ζ₁ ω) s (η₂ ω) (ζ₂ ω) t := by
  have hi₁ := ae_injOn_of_isFlowLine hA25 hκ hκ4 hη₁
  have hi₂ := ae_injOn_of_isFlowLine hA25 hκ hκ4 hη₂
  rcases hx.lt_or_eq with hlt | heq
  · filter_upwards [hi₁, hi₂,
      hW8 κ hκ hκ4 b jumps hb x₁ x₂ θ θ hlt (lt_add_of_pos_right θ Real.pi_pos) P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
      hM κ hκ hκ4 b jumps hb x₁ x₂ θ hlt P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂] with ω hi₁ω hi₂ω hfω hmω
    intro s t hst
    obtain ⟨s₀, t₀, h₀⟩ := hfω (IsInteriorAvailableContact.exists_contact hst)
    have hlt₀ := IsFirstContact.lt_of_isInteriorAvailableContact h₀ hst
    exact agreeAsCurvesAfter_of_isFirstContact hi₁ω hi₂ω h₀ (hmω s₀ t₀ h₀ hlt₀.1 hlt₀.2)
      (Sec7.IsInteriorAvailableContact.mem_stoppedContactSet hst)
  · have hη₁' : IsFlowLine κ b jumps x₂ θ P h η₁ ζ₁ := heq ▸ hη₁
    obtain ⟨Φ, -, hΦ⟩ := hL75 κ hκ hκ4 b jumps hb x₂ θ
    filter_upwards [hi₁, hΦ P h hh η₁ ζ₁ hη₁', hΦ P h hh η₂ ζ₂ hη₂] with ω hi₁ω h₁ω h₂ω
    intro s t hst
    have hζ : ζ₂ ω = ζ₁ ω := h₂ω.1.symm.trans h₁ω.1
    have heqOn : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ ζ₁ ω → η₂ ω r = η₁ ω r := fun r hr =>
      (h₂ω.2 r (by rw [hζ]; exact hr)).symm.trans (h₁ω.2 r hr)
    have ht : (t : ℝ≥0∞) ≤ ζ₁ ω := by rw [← hζ]; exact hst.2.1.le
    have hts : t = s := hi₁ω ht hst.1.le ((heqOn t ht).symm.trans hst.2.2.1.symm)
    subst hts
    rw [hζ]
    exact agreeAsCurvesAfter_self_of_eqOn heqOn ht

/-- **Theorem 1.5 (iii)** (Specification p. 5), with exactly the conclusion of the frozen
`IsFlowLine.crosses_of_lt`, from Theorem W8 (pp. 538–539), Theorem 7.12C (p. 542), the critical exclusion after a
crossing (p. 544) and Aux. lemma 25 (p. 127). -/
theorem crosses_of_lt_of_inputs (hW8 : W8FirstContactStatement.{u})
    (hC : Thm712CCrossingStatement.{u}) (hX : CriticalExclusionAfterCrossingStatement.{u})
    (hA25 : Aux25Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₂ < θ₁) (hθπ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    (∀ᵐ ω ∂P, ∀ s t : ℝ≥0, IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
        ∃ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ ∧
          CrossesFromRightAt (η₁ ω) (ζ₁ ω) s₀ (η₂ ω) (ζ₂ ω) t₀) ∧
      (Real.pi * κ / (4 - κ) ≤ θ₁ - θ₂ → ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        IsInteriorAvailableContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t →
          IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s t) := by
  have hfirst := hW8 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθπ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  refine ⟨?_, fun hcrit => ?_⟩
  · filter_upwards [hfirst, hC κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
      with ω hfω hcω
    intro s t hst
    obtain ⟨s₀, t₀, h₀⟩ := hfω (IsInteriorAvailableContact.exists_contact hst)
    have hlt₀ := IsFirstContact.lt_of_isInteriorAvailableContact h₀ hst
    exact ⟨s₀, t₀, h₀, hcω s₀ t₀ h₀ hlt₀.1 hlt₀.2⟩
  · have hD := (half_le_mul_chiC_div_sleLambda_iff hκ hκ4 _).2 hcrit
    filter_upwards [hfirst,
      hX κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hθπ hD P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
      ae_injOn_of_isFlowLine hA25 hκ hκ4 hη₁, ae_injOn_of_isFlowLine hA25 hκ hκ4 hη₂]
      with ω hfω hxω hi₁ω hi₂ω
    intro s t hst
    obtain ⟨s₀, t₀, h₀⟩ := hfω (IsInteriorAvailableContact.exists_contact hst)
    have hlt₀ := IsFirstContact.lt_of_isInteriorAvailableContact h₀ hst
    have hpt := hxω s₀ t₀ h₀ hlt₀.1 hlt₀.2 s t hst.1.le hst.2.1.le hst.2.2.1 hst.2.2.2
    have hs : s = s₀ := hi₁ω hst.1.le h₀.1 hpt
    have ht : t = t₀ := hi₂ω hst.2.1.le h₀.2.1 (by rw [← hst.2.2.1, hs, h₀.2.2.1])
    rw [hs, ht]
    exact h₀

end Theorem15

end InteractingSLE
