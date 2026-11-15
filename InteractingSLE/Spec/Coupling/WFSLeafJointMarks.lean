/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFS2Kernel
import InteractingSLE.Spec.Coupling.WFSLeafJointGaussian
import InteractingSLE.Spec.Sec7.Lemma725RefMarksGerm

/-!
# Retained germs and nested means for WFS stopped hulls

The new marked-germ theorem and nested Proposition 3.9 apply directly to the
through-coupling API. The announcing sequence is explicit, as in WFS2. These
results retain actual local-set means; they do not identify those means in
swallowed pockets as functions of the stopped driving history.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LQGMetric LocalSets WholeField
open QuantumZipper (H fwdHull zeroGFFTestCov)

section Through

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- The geometry of a measurable stopped-hull version before the cutoff. -/
theorem ae_stoppedHull_geometry_through
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose)
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω) {A : Ω → Set ℂ}
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (Ito.rpath (W · ω)) (τ ω)) :
    ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
  have hgeom := (hC.2.2.2.2.choose_spec _ hτ hτV).1.2.1
  filter_upwards [hgeom, hAK] with ω h1 h2
  rw [h2]
  exact h1

/-- An earlier history-measurable subset's field germ can be retained in the
marks of a WFS stopped hull. The subset premise is pointwise, as in the landed
marked-germ theorem. -/
theorem isHistoryAvoidanceLocal_stoppedHull_sup_germ_through
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : Coupling.IsAnnouncingSeq (drivingFiltration P hC.2.2.2.2.choose) P V σ₀)
    {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose)
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτV : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω) {A E₀ : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (Ito.rpath (W · ω)) (τ ω))
    (hE₀ : Measurable[hτ.measurableSpace, hittingSigma] E₀)
    (hsub : ∀ ω, E₀ ω ∩ H ⊆ A ω) :
    IsHistoryAvoidanceLocal (hτ.measurableSpace ⊔ germSigma E₀ (centredField h u₀))
      A (centredField h u₀) P :=
  Sec7.Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma
    (isZeroBoundaryGFF_centredField_through hC hu₀) hτ.measurableSpace_le hA
    (isHistoryAvoidanceLocal_hull_through hC hκ hu₀ hσ₀ hτ hτV hA hAK) hE₀ hsub

/-- Local-set means at two nested WFS stops exist, and equality of the
complementary covariances forces equality of their pairings. No full-lifetime
restart or full optional-hull coupling is assumed. -/
theorem exists_stoppedHullMeans_flat_through
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
    ∃ gσ gτ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean Aσ (centredField h u₀) P gσ ∧
      IsLocalSetMean Aτ (centredField h u₀) P gτ ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
        zeroGFFTestCov (H \ Aσ ω) φ φ = zeroGFFTestCov (H \ Aτ ω) φ φ → gσ ω φ = gτ ω φ := by
  have hσV : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < V ω :=
    hτV.mono fun ω hω => (ENNReal.coe_le_coe.2 (hστ ω)).trans_lt hω
  have hh := isZeroBoundaryGFF_centredField_through hC hu₀
  have hlocσ := isHistoryAvoidanceLocal_hull_through hC hκ hu₀ hσ₀ hσ hσV hAσ hAσK
  have hlocτ := isHistoryAvoidanceLocal_hull_through hC hκ hu₀ hσ₀ hτ hτV hAτ hAτK
  have hcσ := ae_stoppedHull_geometry_through hC hσ hσV hAσK
  have hcτ := ae_stoppedHull_geometry_through hC hτ hτV hAτK
  have hlσ : IsLocalSet Aσ (centredField h u₀) P :=
    ((isLocalSet_tfae hh hAσ hcσ).out 1 4).1 hlocσ.isAvoidanceLocal
  have hlτ : IsLocalSet Aτ (centredField h u₀) P :=
    ((isLocalSet_tfae hh hAτ hcτ).out 1 4).1 hlocτ.isAvoidanceLocal
  obtain ⟨gσ, hgσ⟩ := IsLocalSet.exists_isLocalSetMean hh hAσ hlσ
  obtain ⟨gτ, hgτ⟩ := IsLocalSet.exists_isLocalSetMean hh hAτ hlτ
  have hℋ := hσ.measurableSpace_mono hτ (fun ω => WithTop.coe_le_coe.2 (hστ ω))
  have hAst : Measurable[hτ.measurableSpace, hittingSigma] Aσ :=
    (measurable_hull_stopping_through hC.1 hC.2.2.2.2.choose hC.2.1 hσ₀ hσ hσV hAσ hAσK).mono
      hℋ le_rfl
  have hsub : ∀ᵐ ω ∂P, Aσ ω ⊆ Aτ ω := by
    filter_upwards [hAσK, hAτK] with ω h1 h2
    rw [h1, h2]
    exact (QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 (hστ ω))
  refine ⟨gσ, gτ, hgσ, hgτ, fun φ => ?_⟩
  exact Sec7.FlatClockProof.IsLocalSetMean.ae_apply_eq_of_zeroGFFTestCov_eq hh hAσ hAτ
    hσ.measurableSpace_le hτ.measurableSpace_le hℋ hlocσ hlocτ hcσ hcτ hsub
    (hAst.comap_le.trans (le_sup_right.trans (le_aeSigma _ P))) hgσ hgτ φ

end Through

end InteractingSLE.WFS
