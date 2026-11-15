/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaPhysical
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaVersions
import InteractingSLE.Spec.Supplement.GW4SafeREtaMean

/-! # GW4: reference union laws for the very means used in transport -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Sec7.Aux119Heights Sec7.SideC12 GW4Rel

/-- The inverted original union means, after centering, agree with actual
means of the literal physical union. Hence the Prop. 3.8 reference laws and
the component transport use the same means, despite different set versions. -/
theorem exists_physical_union_reference_means
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling (16 / κ) xL xR ρL ρR P 𝓕 W VL VR B ζ
      (fun ω => invField κ (h ω)))
    {u₀ u₁ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₁ : IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) ρL ρR xL xR) (forceJumpSet xL xR) u₁)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {E : Ω → Set ℂ} (hEm : Measurable[mΩ, hittingSigma] E)
    (hEd : MeasurableSpace.comap E hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField (fun ω => invField κ (h ω)) u₁) inferInstance) P)
    (hEl : IsLocalSet E (centredField (fun ω => invField κ (h ω)) u₁) P)
    {K A : ℚ → Ω → Set ℂ} (hKm : ∀ s, Measurable[mΩ, hittingSigma] (K s))
    (hKeq : ∀ s : ℚ, ∀ᵐ ω ∂P,
      K s ω = fwdHull (fun r : ℝ => W r.toNNReal ω) (s : ℝ).toNNReal)
    (hAm : ∀ s, Measurable[mΩ, hittingSigma] (A s))
    (hAc : ∀ s ω, A s ω ⊆ H ∧ IsOpen (H \ A s ω))
    (hAE : ∀ s, (fun ω => WangWu.negInv '' A s ω) =ᵐ[P] (fun ω => E ω ∪ K s ω))
    {M : ℚ → Ω → DistOn upperHalfPlaneOpens}
    (hM : ∀ s, IsLocalSetMean (A s) (centredField h u₀) P
      (fun ω => M s ω - smoothDist upperHalfPlaneOpens u₀)) :
    ∃ G : ℚ → Ω → DistOn upperHalfPlaneOpens,
      (∀ s, IsLocalSetMean (fun ω => E ω ∪ K s ω)
        (centredField (fun ω => invField κ (h ω)) u₁) P (G s)) ∧
      ∀ᵐ ω ∂P, ∀ s : ℚ,
        G s ω = invField κ (M s ω) - smoothDist upperHalfPlaneOpens u₁ ∧
        ∀ z ∈ H \ (E ω ∪ K s ω),
          harmRep (G s ω) (H \ (E ω ∪ K s ω)) z + u₁ z =
            harmRep (invField κ (M s ω)) (WangWu.negInv '' (H \ A s ω)) z := by
  have hh0 := WholeField.isZeroBoundaryGFF_centredField hC hu₁
  have hKl (s : ℚ) : IsLocalSet (K s) (centredField (fun ω => invField κ (h ω)) u₁) P :=
    Sec7.R5Same.isLocalSet_hull hC hu₁ hX (s : ℝ).toNNReal
      (hζ.mono fun _ hω => hω ▸ ENNReal.coe_lt_top) (hKeq s)
  have hUnion (s : ℚ) := IsLocalSet.isLocalSet_union hh0 hEm (hKm s)
    (Sec6.condIndepEv_of_le_aeSigma hh0.measurable.comap_le (hKm s).comap_le hEd) hEl (hKl s)
  choose G hG using (fun s : ℚ => IsLocalSet.exists_isLocalSetMean hh0
    (measurable_union_hitting hEm (hKm s)) (hUnion s))
  have hPhys (s : ℚ) := localSetMean_invField hκ (hAc s) hu₀ hu₁.1 (hM s)
  have hEq (s : ℚ) := ae_localSetMean_eq_of_ae_set_eq hh0
    (WangWu.measurable_image_negInv.comp (hAm s)) (measurable_union_hitting hEm (hKm s))
    (Eventually.of_forall fun ω => (WangWu.image_negInv_relClosed (hAc s ω)).2)
    ((hUnion s).2.1.mono fun _ hω => hω.2) (hAE s) (hPhys s) (hG s)
  refine ⟨G, hG, ?_⟩
  have hall := ae_all_iff.2 fun s : ℚ => (hEq s).and ((hAE s).and (hPhys s).2.1)
  filter_upwards [hall] with ω hω s
  obtain ⟨hEqω, hAEω, hHarm⟩ := hω s
  refine ⟨hEqω.symm, fun z hz => ?_⟩
  have hU : H \ (E ω ∪ K s ω) = WangWu.negInv '' (H \ A s ω) := by
    rw [← hAEω, WangWu.H_diff_image_negInv]
  have hUo := (WangWu.image_negInv_relClosed (hAc s ω)).2
  have hz' : z ∈ H \ WangWu.negInv '' A s ω := hAEω.symm ▸ hz
  have hAdd := harmRep_add_smoothDist hUo sdiff_subset hHarm hu₁.1 hz'
  simp only [sub_add_cancel] at hAdd
  rw [hEqω, hAEω] at hAdd
  rw [← hU]
  exact hAdd.symm

end InteractingSLE.Theorem14.GW4Fix
