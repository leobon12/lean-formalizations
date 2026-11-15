/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualLines

/-!
# Physical observations from the landed flow-line and chart results

Packet PROVE-RETPLUMB. Choose the existing continuous capped versions, recover
the initial chart by the landed history adapter, and construct the actual physical
prefix observations. No chart, clock, safe-event or future-lifetime measurability
premise remains in this constructor.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open Supp7 Sec7.Lemma76F LocalSets
open LQGMetric (DistOn)
universe v
variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The actual physical observation proposition follows from the landed
flow-line and initial-chart results on an initial event of good disjoint pairs. -/
theorem retPrefixObservations_of_flowLines
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ η₁' η₂' : Ω → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} {G : ℝ≥0 → Set Ω} {u r : ℝ≥0} {F : Set Ω}
    (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    (ha₂ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → η₂' ω s = η₂ ω s)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hGsub : G r ⊆ {ω | (u : ℝ≥0∞) < ζ₁ ω ∧ (r : ℝ≥0∞) < ζ₂ ω})
    (hGae : ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω → ω ∈ G r)
    (hF : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r] F) (hG : F ⊆ G r)
    (hp₁ : ∀ ω ∈ F, IsPathGood (η₁' ω) (ζ₁ ω) x₁)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) :
    RetPrefixObservations (retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r) F G η₁' η₂' ζ₂ u r := by
  classical
  choose α₁ hc₁ hm₁ h0₁ hconst₁ hag₁ hfac₁ hζfac₁ using fun t : ℝ≥0 =>
    exists_capped_version hL75 hκ hκ4 hb hh hη₁ (fun _ => 0) (capR u (r + t))
  choose α₂ hc₂ hm₂ h0₂ hconst₂ hag₂ hfac₂ hζfac₂ using fun t : ℝ≥0 =>
    exists_capped_version hL75 hκ hκ4 hb hh hη₂ (fun _ => 0) (capR u (r + t))
  have hag : ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω →
      ω ∈ G r ∧ (∀ s ≤ u, η₁' ω s = η₁ ω s) ∧ ∀ s ≤ r, η₂' ω s = η₂ ω s := by
    filter_upwards [hGae, ha₁, ha₂] with ω hg he₁ he₂ hu hr
    exact ⟨hg hu hr, fun s hs => he₁ s ((ENNReal.coe_le_coe.2 hs).trans hu.le),
      fun s hs => he₂ s ((ENNReal.coe_le_coe.2 hs).trans hr.le)⟩
  have hac₁ : ∀ᵐ ω ∂P, ∀ s, α₁ 0 ω s = η₁ ω (capTime (capR u r) (ζ₁ ω) s) := by
    simpa only [add_zero] using hag₁ 0
  have hac₂ : ∀ᵐ ω ∂P, ∀ s, α₂ 0 ω s = η₂ ω (capTime (capR u r) (ζ₂ ω) s) := by
    simpa only [add_zero] using hag₂ 0
  obtain ⟨hdom, hfwd, -⟩ := chart_measurability_retSigma76 hd
    (measurable_lifetime_of_isFlowLine hη₁) (measurable_lifetime_of_isFlowLine hη₂)
    hGsub hag (hc₁ 0) (hc₂ 0) (hm₁ 0) (hm₂ 0) (h0₁ 0) (h0₂ 0) hac₁ hac₂
  have hde (z : ℂ) : {ω | z ∈ ((retFam G η₁' η₂' u r).chart ω).dom} =
      {ω | z ∈ (retFam G η₁' η₂' u r).D ω} := by
    ext ω
    change z ∈ ((retFam G η₁' η₂' u r).chart ω).dom ↔ z ∈ (retFam G η₁' η₂' u r).D ω
    rw [← SetLike.mem_coe, hd.coe_dom_chart ω]
  apply retPrefixObservations_retPhysFiltration hd hF hG
    (measurable_lifetime_of_isFlowLine hη₂) ha₁ ha₂ hp₁ hp₂ hpair
    α₁ α₂ hc₁ hc₂ hm₁ hm₂ hag₁ hag₂
  · intro z
    rw [← hde z]
    exact hdom z
  · intro z
    rw [← hde z]
    exact hfwd z

end InteractingSLE.Restart.RetAux79
