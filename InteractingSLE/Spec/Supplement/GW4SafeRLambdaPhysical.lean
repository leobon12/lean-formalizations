/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRThetaInversion

/-! # GW4: the actual centered ambient union mean after inversion -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open QuantumZipper (H chiC)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField GW4Rel Sec7.SideC12
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- Restoring the original background, applying the prescribed source
inversion and removing the ambient background transports the full
local-set-mean law. -/
theorem localSetMean_invField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} (hκ : 0 < κ) {A : Ω → Set ℂ}
    (hA : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    {h M : Ω → DistOn upperHalfPlaneOpens} {u₀ u₁ : ℂ → ℝ}
    (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₁ : InnerProductSpace.HarmonicOnNhd u₁ H)
    (hM : IsLocalSetMean A (centredField h u₀) P
      (fun ω => M ω - smoothDist upperHalfPlaneOpens u₀)) :
    IsLocalSetMean (fun ω => WangWu.negInv '' A ω)
      (centredField (fun ω => invField κ (h ω)) u₁) P
      (fun ω => invField κ (M ω) - smoothDist upperHalfPlaneOpens u₁) := by
  have hT := fun ω => isChartTransport_invField hκ (h ω)
  have hTr : ∀ ω, IsTranslateAddConst 0 0 (invField κ (h ω)) (invField κ (h ω)) :=
    fun ω => by simpa only [zero_mul] using
      Sec7.StripSysField.isTranslateAddConst_zero_self (invField κ (h ω)) 0
  have hp := localSetMean_physicalMean hA hT hTr hu₀ hu₁ hM
  have heq : (fun ω => physicalMean (-(Real.pi * chiC κ)) (chiC (16 / κ)) 0
      u₀ u₁ (M ω - smoothDist upperHalfPlaneOpens u₀)) =
      (fun ω => invField κ (M ω) - smoothDist upperHalfPlaneOpens u₁) := by
    funext ω
    have hTrM : IsTranslateAddConst 0 0 (invField κ (M ω)) (invField κ (M ω)) := by
      simpa only [zero_mul] using Sec7.StripSysField.isTranslateAddConst_zero_self (invField κ (M ω)) 0
    rw [field_eq_reflect_add (isChartTransport_invField hκ (M ω)) hTrM]
    simp only [physicalMean, sub_add_cancel]
    have hsub : smoothDist upperHalfPlaneOpens
        (sourceShift (-(Real.pi * chiC κ)) (chiC (16 / κ)) 0 - u₁) =
        smoothDist upperHalfPlaneOpens (sourceShift (-(Real.pi * chiC κ)) (chiC (16 / κ)) 0) -
          smoothDist upperHalfPlaneOpens u₁ := by
      ext φ
      rw [sub_apply, Coupling.smoothDist_apply_eq
        ((sourceShift_harmonic _ _ _).sub hu₁).continuousOn,
        Coupling.smoothDist_apply_eq (sourceShift_harmonic _ _ _).continuousOn,
        Coupling.smoothDist_apply_eq hu₁.continuousOn]
      simp_rw [Pi.sub_apply, sub_mul]
      exact integral_sub
        (Coupling.MartMeans2.integrable_mul_test_of_continuousOn
          (sourceShift_harmonic _ _ _).continuousOn φ φ.tsupport_subset)
        (Coupling.MartMeans2.integrable_mul_test_of_continuousOn hu₁.continuousOn φ φ.tsupport_subset)
    rw [hsub]
    abel
  rwa [heq] at hp

end InteractingSLE.Theorem14.GW4Fix
