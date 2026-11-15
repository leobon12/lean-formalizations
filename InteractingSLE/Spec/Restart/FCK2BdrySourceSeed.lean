/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2BdryVisit

/-!
# Source seed admissibility, including collapsed sides

A collapsed side maps zero to an original real endpoint. Both source flow
lines visit that endpoint strictly before their lifetimes. The live-visit
bounds therefore supply the original incident inequalities for both angles.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open LQGMetric (DistOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb
open PiecewiseConstantBoundaryData
universe u

/-- At a collapsed first-contact side, the original boundary satisfies the
incident strict inequalities for both source angles. -/
theorem ae_original_incident_bounds_of_firstContact
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      (d.wordL ω = 0 →
        (leftLim b (d.baseL ω) + θ₁ * chiC κ < sleLambda κ) ∧
        (leftLim b (d.baseL ω) + θ₂ * chiC κ < sleLambda κ)) ∧
      (d.wordR ω = 0 →
        (-sleLambda κ < rightLim b (d.baseR ω) + θ₁ * chiC κ) ∧
        (-sleLambda κ < rightLim b (d.baseR ω) + θ₂ * chiC κ)) := by
  have hv₁ := ae_live_real_incident_bounds hκ hκ4 hb hh hη₁
  have hv₂ := ae_live_real_incident_bounds hκ hκ4 hb hh hη₂
  have hp₁ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁
  have hp₂ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂
  filter_upwards [hae, hv₁, hv₂, hp₁, hp₂] with ω ha hv₁ω hv₂ω hp₁ω hp₂ω hM
  obtain ⟨hE, hs, ht⟩ := mem_meetSet_iff.1 hM
  have hs' : (d.s₀ ω : ℝ≥0∞) < ζ₁ ω := by rwa [← hζ₁]
  have ht' : (d.t₀ ω : ℝ≥0∞) < ζ₂ ω := by rwa [← hζ₂]
  have hzero₁ : d.η₁ ω 0 = (x₁ : ℂ) :=
    (ha.2.1 0 (by simp)).trans (Sec7.IsPathGood.zero hp₁ω)
  have hzero₂ : d.η₂ ω 0 = (x₂ : ℂ) :=
    (ha.2.2 0 (by simp)).trans (Sec7.IsPathGood.zero hp₂ω)
  have hx₁K : (x₁ : ℂ) ∈ d.K ω := by
    rw [PairData.K_of_mem hE, prefixSet]
    exact Or.inl ⟨0, ⟨le_rfl, zero_le⟩, hzero₁⟩
  have hx₂K : (x₂ : ℂ) ∈ d.K ω := by
    rw [PairData.K_of_mem hE, prefixSet]
    exact Or.inr ⟨0, ⟨le_rfl, zero_le⟩, hzero₂⟩
  have hL₂ : d.baseL ω ≤ x₂ := hd.baseL_le hx₂K
  have hR₁ : x₁ ≤ d.baseR ω := hd.le_baseR hx₁K
  have hc := contact_eq_base_of_collapsed hd hE
  have he := (hd.isFirstContact hE).2.2.1
  have hv (y : ℝ) (hy : d.η₁ ω (d.s₀ ω) = (y : ℂ)) :
      ((y ≤ x₁ → leftLim b y + θ₁ * chiC κ < sleLambda κ) ∧
        (x₁ ≤ y → -sleLambda κ < rightLim b y + θ₁ * chiC κ)) ∧
      ((y ≤ x₂ → leftLim b y + θ₂ * chiC κ < sleLambda κ) ∧
        (x₂ ≤ y → -sleLambda κ < rightLim b y + θ₂ * chiC κ)) := by
    exact ⟨hv₁ω _ hs' y ((ha.2.1 _ hs'.le).symm.trans hy),
      hv₂ω _ ht' y ((ha.2.2 _ ht'.le).symm.trans (he.symm.trans hy))⟩
  exact ⟨fun hL => ⟨(hv _ (hc.1 hL)).1.1 (hL₂.trans hx.le),
      (hv _ (hc.1 hL)).2.1 hL₂⟩,
    fun hR => ⟨(hv _ (hc.2 hR)).1.2 hR₁,
      (hv _ (hc.2 hR)).2.2 (hx.le.trans hR₁)⟩⟩

/-- Both source seeds are admissible, including either collapsed side. -/
theorem ae_admissible_of_boxMean_all_sides
    (h75 : Theorem15.Lemma75Statement.{u}) (h77 : Supp10.Lemma77Statement.{u})
    (h56 : RetainedRangeEntranceStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps)
    {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧
      (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {β : Ω → BoundaryWord} (hs : ∀ᵐ ω ∂P, ω ∈ meetSet d → (β ω).IsSorted)
    (hm : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      ExplState.IsAdmissibleSeed κ (leftLim (β ω).fn 0) (rightLim (β ω).fn 0) θ₁ ∧
      ExplState.IsAdmissibleSeed κ (leftLim (β ω).fn 0) (rightLim (β ω).fn 0) θ₂ := by
  have hi := ae_incident_heights_of_boxMean h75 h77 h56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hd
    hζ₁ hζ₂ hae hu₀ hs hm
  have hv := ae_original_incident_bounds_of_firstContact hκ hκ4 hb hx hh hη₁ hη₂ hd hζ₁ hζ₂ hae
  filter_upwards [hi, hv] with ω hiω hvω hM
  have hi' := hiω hM
  have hv' := hvω hM
  exact ⟨(admissible_iff_original_incident_bounds hκ hκ4 hθ (Or.inl rfl) d ω (β ω)
      hi'.1 hi'.2).2 ⟨fun he => (hv'.1 he).1, fun he => (hv'.2 he).1⟩,
    (admissible_iff_original_incident_bounds hκ hκ4 hθ (Or.inr rfl) d ω (β ω)
      hi'.1 hi'.2).2 ⟨fun he => (hv'.1 he).2, fun he => (hv'.2 he).2⟩⟩

end InteractingSLE.Restart.FCPlumb
