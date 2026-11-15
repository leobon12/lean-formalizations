/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafJointMarks
import InteractingSLE.Spec.Supplement.WalkStageLocalAE

/-!
# Retaining earlier hull germs with almost-sure nesting

Measurable hull versions are nested almost surely. Taking their union makes
nesting pointwise without changing the larger hull almost surely, so the
landed marked-germ theorem applies to the actual, unmodified smaller germ.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LQGMetric LocalSets WholeField
open QuantumZipper (H fwdHull zeroGFFTestCov)

/-- The marked-germ theorem with almost-sure inclusion. Only the larger set is
temporarily replaced, so no equality of germ sigma algebras under null
modifications is needed. -/
theorem isHistoryAvoidanceLocal_sup_germSigma_of_ae_subset
    {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hℋ : ℋ ≤ mΩ)
    {E E₀ : Ω → Set ℂ} (hE : Measurable[mΩ, hittingSigma] E)
    (hloc : IsHistoryAvoidanceLocal ℋ E h P)
    (hE₀ : Measurable[ℋ, hittingSigma] E₀) (hsub : ∀ᵐ ω ∂P, E₀ ω ⊆ E ω) :
    IsHistoryAvoidanceLocal (ℋ ⊔ germSigma E₀ h) E h P := by
  have heq : E =ᵐ[P] (fun ω => E ω ∪ E₀ ω) :=
    hsub.mono fun _ hω => (union_eq_left.2 hω).symm
  have hloc' := Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae heq hloc
  have hret := Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℋ
    (measurable_union_hitting hE (hE₀.mono hℋ le_rfl)) hloc' hE₀
    (fun _ => inter_subset_left.trans subset_union_right)
  exact Theorem14.WalkLaw.isHistoryAvoidanceLocal_congr_ae heq.symm hret

section Through

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- The later stopped hull is local with the earlier hull's actual field germ
retained alongside the later driving history. -/
theorem isHistoryAvoidanceLocal_nestedHullGerm_through
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : Coupling.IsAnnouncingSeq (drivingFiltration P hC.2.2.2.2.choose) P V σ₀)
    {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose)
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hτ : IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose)
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hστ : ∀ ω, σ ω ≤ τ ω) (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω)
    {Aσ Aτ : Ω → Set ℂ} (hAσ : Measurable[mΩ, hittingSigma] Aσ)
    (hAτ : Measurable[mΩ, hittingSigma] Aτ)
    (hAσK : ∀ᵐ ω ∂P, Aσ ω = fwdHull (Ito.rpath (W · ω)) (σ ω))
    (hAτK : ∀ᵐ ω ∂P, Aτ ω = fwdHull (Ito.rpath (W · ω)) (τ ω)) :
    IsHistoryAvoidanceLocal (hτ.measurableSpace ⊔ germSigma Aσ (centredField h u₀))
      Aτ (centredField h u₀) P := by
  have hσV : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < V ω :=
    hτV.mono fun ω hω => (ENNReal.coe_le_coe.2 (hστ ω)).trans_lt hω
  have hAst : Measurable[hτ.measurableSpace, hittingSigma] Aσ :=
    (measurable_hull_stopping_through hC.1 hC.2.2.2.2.choose hC.2.1 hσ₀ hσ hσV hAσ hAσK).mono
      (hσ.measurableSpace_mono hτ (fun ω => WithTop.coe_le_coe.2 (hστ ω))) le_rfl
  have hsub : ∀ᵐ ω ∂P, Aσ ω ⊆ Aτ ω := by
    filter_upwards [hAσK, hAτK] with ω h1 h2
    rw [h1, h2]
    exact (QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 (hστ ω))
  exact isHistoryAvoidanceLocal_sup_germSigma_of_ae_subset
    (isZeroBoundaryGFF_centredField_through hC hu₀) hτ.measurableSpace_le hAτ
    (isHistoryAvoidanceLocal_hull_through hC hκ hu₀ hσ₀ hτ hτV hAτ hAτK) hAst hsub

end Through

end InteractingSLE.WFS
