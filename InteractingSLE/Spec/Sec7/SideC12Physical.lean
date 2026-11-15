/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Transport
import InteractingSLE.Spec.Sec7.PocketStopWallsFinReflect

/-!
# The actual centered counterflow mean from an original local mean

PROVE-SIDE-COLLAR2. The frozen infinity-source transport and zero spatial
translation determine the harmonic correction. Its lift is evaluated at
the inverse coordinate. The resulting distribution is a local-set mean
of the actual centered counterflow field, with its pointwise physical
mean formula. No mean-transport or background-matching hypothesis is used.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.SideC12

open LocalSets Aux119Heights WholeField
open WangWu (negInv reflectField)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- The additive part of the infinity-source transport, in the target
coordinate, including the subsequent constant translation. -/
def sourceShift (a k c : ℝ) (z : ℂ) : ℝ :=
  a + k * infinitySourceChart.2.2 (negInv z) + c

theorem sourceShift_harmonic (a k c : ℝ) :
    InnerProductSpace.HarmonicOnNhd (sourceShift a k c) H := by
  have hL : InnerProductSpace.HarmonicOnNhd
      (fun z => infinitySourceChart.2.2 (negInv z)) H :=
    LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H
      StripSysField.harmonicOnNhd_infinitySourceChart_lift
      Chart.isConformal_infinitySourceChart.1 Chart.isConformal_infinitySourceChart.2.1
  intro z hz
  have hk := (hL z hz).const_smul (c := k)
  convert ((InnerProductSpace.harmonicAt_const a).add hk).add
      (InnerProductSpace.harmonicAt_const c) using 1
  funext w
  simp only [sourceShift, Pi.smul_apply, smul_eq_mul, Pi.add_apply]

/-- The two frozen field relations are exactly inversion plus the
explicit smooth harmonic shift. -/
theorem field_eq_reflect_add {a k c : ℝ}
    {h h' h'' : DistOn upperHalfPlaneOpens}
    (hT : IsChartTransport infinitySourceChart (-1) a k h h')
    (hTr : IsTranslateAddConst 0 c h' h'') :
    h'' = reflectField h + smoothDist upperHalfPlaneOpens (sourceShift a k c) := by
  ext φ
  have he := hTr φ φ (fun z => by simp)
  rw [he, hT.apply_eq Chart.isConformal_infinitySourceChart,
    add_apply, WangWu.reflectField_apply,
    PocketStopWallsFin.pushTest_return_eq_source',
    Coupling.smoothDist_apply_eq (sourceShift_harmonic a k c).continuousOn]
  have h0 : Integrable fun z => φ z :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hL := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
    (sourceShift_harmonic 0 1 0).continuousOn φ φ.tsupport_subset
  simp only [sourceShift, zero_add, one_mul, add_zero] at hL
  have hi : (∫ z, sourceShift a k c z * φ z) =
      a * (∫ z, φ z) + k * (∫ z, infinitySourceChart.2.2 (negInv z) * φ z) + c * (∫ z, φ z) := by
    simp only [sourceShift, add_mul, mul_assoc]
    have hiadd := integral_add ((h0.const_mul a).add (hL.const_mul k)) (h0.const_mul c)
    simp only [Pi.add_apply] at hiadd
    rw [hiadd, integral_add (h0.const_mul a) (hL.const_mul k), integral_const_mul,
      integral_const_mul, integral_const_mul]
  rw [hi]
  have hInv : infinitySourceChart.2.1 = negInv := rfl
  rw [hInv]
  ring

/-- The transported centered local mean. The original background is
first restored, and the actual counterflow background is then removed. -/
def physicalMean (a k c : ℝ) (u₀ u₁ : ℂ → ℝ)
    (g : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  reflectField (g + smoothDist upperHalfPlaneOpens u₀) +
    smoothDist upperHalfPlaneOpens (sourceShift a k c - u₁)

theorem localSetMean_physicalMean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → Set ℂ} (hA : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    {h h' h'' g : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    {u₀ u₁ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₁ : InnerProductSpace.HarmonicOnNhd u₁ H)
    (hg : IsLocalSetMean A (centredField h u₀) P g) :
    IsLocalSetMean (fun ω => negInv '' A ω) (centredField h'' u₁) P
      (fun ω => physicalMean a k c u₀ u₁ (g ω)) := by
  have hFull := localSetMean_add_dist (fun ω => (hA ω).2) hg
    (isHarmonicDistOn_smoothDist hu₀)
  have hf : (fun ω => centredField h u₀ ω + smoothDist upperHalfPlaneOpens u₀) = h := by
    funext ω
    exact sub_add_cancel _ _
  rw [hf] at hFull
  have hResult := localSetMean_reflect_add hA hFull ((sourceShift_harmonic a k c).sub hu₁)
  have hFields : (fun ω => reflectField (h ω) +
      smoothDist upperHalfPlaneOpens (sourceShift a k c - u₁)) = centredField h'' u₁ := by
    funext ω
    rw [centredField, field_eq_reflect_add (hT ω) (hTr ω)]
    have hs : smoothDist upperHalfPlaneOpens (sourceShift a k c - u₁) =
        smoothDist upperHalfPlaneOpens (sourceShift a k c) - smoothDist upperHalfPlaneOpens u₁ := by
      ext φ
      rw [sub_apply, Coupling.smoothDist_apply_eq ((sourceShift_harmonic a k c).sub hu₁).continuousOn,
        Coupling.smoothDist_apply_eq (sourceShift_harmonic a k c).continuousOn,
        Coupling.smoothDist_apply_eq hu₁.continuousOn]
      simp_rw [Pi.sub_apply, sub_mul]
      exact integral_sub
        (Coupling.MartMeans2.integrable_mul_test_of_continuousOn
          (sourceShift_harmonic a k c).continuousOn φ φ.tsupport_subset)
        (Coupling.MartMeans2.integrable_mul_test_of_continuousOn hu₁.continuousOn φ φ.tsupport_subset)
    rw [hs]
    abel
  rwa [hFields] at hResult

/-- Exact physical means, simultaneously on the entire random
complement. The deterministic backgrounds cancel with their correct signs. -/
theorem ae_physicalMean_formula {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → Set ℂ} (hA : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    {h g : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    {u₀ u₁ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₁ : InnerProductSpace.HarmonicOnNhd u₁ H)
    (hg : IsLocalSetMean A (centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ∀ z ∈ H \ negInv '' A ω,
      harmRep (physicalMean a k c u₀ u₁ (g ω)) (H \ negInv '' A ω) z + u₁ z =
        -(harmRep (g ω) (H \ A ω) (negInv z) + u₀ (negInv z)) + sourceShift a k c z := by
  have hFull := localSetMean_add_dist (fun ω => (hA ω).2) hg
    (isHarmonicDistOn_smoothDist hu₀)
  have hRep := ae_harmRep_reflect_add hA hFull ((sourceShift_harmonic a k c).sub hu₁)
  filter_upwards [hg.2.1, hRep] with ω hgω hRepω z hz
  have hzR : negInv z ∈ H \ A ω := by
    rw [WangWu.H_diff_image_negInv] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa only [WangWu.negInv_negInv] using hw
  change harmRep (reflectField (g ω + smoothDist upperHalfPlaneOpens u₀) +
    smoothDist upperHalfPlaneOpens (sourceShift a k c - u₁))
      (H \ negInv '' A ω) z + u₁ z = _
  rw [hRepω z hz]
  change -(harmRep (g ω + smoothDist upperHalfPlaneOpens u₀) (H \ A ω) (negInv z)) +
    (sourceShift a k c z - u₁ z) + u₁ z = _
  rw [harmRep_add_smoothDist (hA ω).2 sdiff_subset hgω hu₀ hzR]
  dsimp only
  ring

end InteractingSLE.Sec7.SideC12
