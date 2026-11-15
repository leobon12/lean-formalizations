/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.KernelTower2
import InteractingSLE.Spec.Sec7.R5EnlTrace
import InteractingSLE.Spec.Sec6.Aux27Germ

/-! # GW4: local means of almost surely equal set versions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter MeasureTheory
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets

/-- Almost surely equal retained sets have null-equivalent germ records.
This uses the existing exact trace theorem and retains the full field. -/
theorem germSigma_le_aeSigma_of_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A B : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (he : A =ᵐ[P] B) : germSigma A h ≤ aeSigma (germSigma B h) P := by
  let D := {ω | A ω = B ω}
  have htr := Sec7.R5Enl.comap_val_germSigma_congr (h := h) (E := D) (fun _ hω => hω)
  intro U hU
  have hu : MeasurableSet[MeasurableSpace.comap ((↑) : D → Ω) (germSigma A h)]
      (((↑) : D → Ω) ⁻¹' U) := ⟨U, hU, rfl⟩
  rw [htr] at hu
  obtain ⟨V, hV, hVU⟩ := hu
  refine ⟨V, hV, ?_⟩
  filter_upwards [he] with ω hω
  exact propext (Set.ext_iff.1 hVU (⟨ω, hω⟩ : D)).symm

/-- Versions of one physical local set have the same distribution-valued
mean almost surely. Exact germ measurability of either version is preserved;
the equality is obtained by comparing conditional expectations on their
null-equivalent germ records. -/
theorem ae_localSetMean_eq_of_ae_set_eq {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h gA gB : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    {A B : Ω → Set ℂ} (hAm : Measurable[mΩ, hittingSigma] A)
    (hBm : Measurable[mΩ, hittingSigma] B)
    (hAo : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) (hBo : ∀ᵐ ω ∂P, IsOpen (H \ B ω))
    (hAB : A =ᵐ[P] B) (hgA : IsLocalSetMean A h P gA)
    (hgB : IsLocalSetMean B h P gB) : gA =ᵐ[P] gB := by
  have hAl := germSigma_le hAm hh.measurable
  have hBl := germSigma_le hBm hh.measurable
  have hAtoB := germSigma_le_aeSigma_of_ae_eq (h := h) hAB
  have hBtoA := germSigma_le_aeSigma_of_ae_eq (h := h) hAB.symm
  have he (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
      (fun ω => gA ω φ) =ᵐ[P] fun ω => gB ω φ := by
    have hi := (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
    have h1 := Sec6.IsLocalSetMean.ae_eq_condExp hAm hh.measurable hgA hAo φ hi
    have h2 := Sec6.IsLocalSetMean.ae_eq_condExp hBm hh.measurable hgB hBo φ hi
    have hs := sup_le hAl hBl
    have htrA := sup_le (le_aeSigma (germSigma A h) P) hBtoA
    have htrB := sup_le hAtoB (le_aeSigma (germSigma B h) P)
    exact h1.trans ((KernelTower.condExp_ae_eq_of_le_aeSigma_sup le_sup_left hs htrA hi).trans
      ((KernelTower.condExp_ae_eq_of_le_aeSigma_sup le_sup_right hs htrB hi).symm.trans h2.symm))
  filter_upwards [ae_all_iff.2 (fun j : ℕ × ℕ => he (LQGMetric.distGen upperHalfPlaneOpens j))]
    with ω hω
  exact LQGMetric.injective_distOn_pairings upperHalfPlaneOpens (funext hω)

end InteractingSLE.Theorem14.GW4Fix
