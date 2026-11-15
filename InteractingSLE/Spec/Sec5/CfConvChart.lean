/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvRegular

/-!
# The exact field shift and infinite-lifetime chart clause

Packet PROVE-CFCHART2. The mean integrand is integrable on every chart-avoidance event, by
continuity on the compact support of the test function. Consequently the constant field shift
requires no additional integrability premise. Null modification gives an infinite-lifetime
clause for a driver continuous at every sample.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfConv

open CfGiven CfChart Restart.DomainMarkov Coupling.MartMeans2

section Mean

variable {κ a k : ℝ} {w : ℝ≥0 → ℝ} {c : Chart} {u : ℂ → ℝ}

/-- The tested chart mean is integrable whenever the test support avoids the hull. -/
theorem integrable_chartMean (hc : c.IsConformal) (hlift : ContinuousOn c.2.2 c.dom)
    (hw : Continuous w) (hu : InnerProductSpace.HarmonicOnNhd u H) (t : ℝ≥0)
    (φ : TestOn upperHalfPlaneOpens)
    (hφ : tsupport φ ⊆ c.2.1 '' (H \ fwdHull (Ito.rpath w) (t : ℝ))) :
    Integrable fun z => (couplingMean κ (Ito.rpath w) (t : ℝ) u (c.1 z) - a - k * c.2.2 z) * φ z := by
  have hr : ContinuousOn (Ito.rpath w) (Icc 0 (t : ℝ)) :=
    (hw.comp continuous_real_toNNReal).continuousOn
  have hdom : c.2.1 '' (H \ fwdHull (Ito.rpath w) (t : ℝ)) ⊆ c.dom := by
    rw [hc.coe_dom]
    exact image_mono sdiff_subset
  have hm : MapsTo c.1 (c.2.1 '' (H \ fwdHull (Ito.rpath w) (t : ℝ))) (Coupling.hullDom w t) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hc.2.2 z hz.1]
    exact Coupling.mem_hullDom hr hz.1 hz.2
  exact integrable_mul_test_of_continuousOn
    ((((Coupling.continuousOn_couplingMean κ hr hu).comp
      (hc.differentiableOn_fwd.continuousOn.mono hdom) hm).sub continuousOn_const).sub
      (continuousOn_const.mul (hlift.mono hdom))) φ hφ

end Mean

section Shift

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {κ θ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {h h' : Ω → DistOn upperHalfPlaneOpens}

/-- Remove the angle shift from the field, obtaining exactly the constants `(-πχ, -χ)`. -/
theorem IsChartCanon.unshift_field (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (h' ω))
    (hc : ∀ ω, (c ω).IsConformal) (hlift : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hWc : ∀ ω, Continuous fun t => W t ω)
    (hcan : IsChartCanon (16 / κ) ρL ρR P 𝓐 W VL VR ζ c
      (-((π - θ) * chiC κ)) (-chiC κ) (fun ω => -h' ω)) :
    IsChartCanon (16 / κ) ρL ρR P 𝓐 W VL VR ζ c (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) := by
  have hshift : ∀ ω (φ : TestOn upperHalfPlaneOpens), (-h ω) φ = (-h' ω) φ + (θ * chiC κ) * ∫ z, φ z := by
    intro ω φ
    have hφ := htr ω φ φ (fun z => by rw [Complex.ofReal_zero, add_zero])
    change -(h ω φ) = -(h' ω φ) + (θ * chiC κ) * ∫ z, φ z
    linarith only [hφ]
  have he := CfChart.IsChartCanon.shift_field (θ * chiC κ) hcan hshift (fun t φ => by
    exact Eventually.of_forall fun ω hE => integrable_chartMean (hc ω) (hlift ω) (hWc ω)
      (isBoundedHarmonicExtension_bheProc (κ := 16 / κ) (ρL := ρL) (ρR := ρR)
        (W := W) (VL := VL) (VR := VR) ω t).1 t φ hE.2)
  have ha : -((π - θ) * chiC κ) - θ * chiC κ = -(π * chiC κ) := by ring
  rwa [ha] at he

end Shift

section Regularize

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {nL nR : ℕ} {κ a k : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {h : Ω → DistOn upperHalfPlaneOpens}

/-- Regularize the driver and remove an almost surely infinite killing time, preserving the chart clause. -/
theorem IsChartCanon.regularize_top {A : Set Ω} (hA : MeasurableSet A) (hAe : ∀ᵐ ω ∂P, ω ∈ A)
    (hζ : ∀ ω ∈ A, ζ ω = ⊤) (hh : Measurable h)
    (hcan : IsChartCanon κ ρL ρR P 𝓐 W VL VR ζ c a k h) :
    IsChartCanon κ ρL ρR P (eventFiltration 𝓐 A hA) (eventDriver A W) VL VR
      (fun _ => ⊤) c a k h := by
  have hc := CfChart.IsChartCanon.of_le_aeSigma hcan hh
    (le_eventFiltration 𝓐 A hA) (eventFiltration_le_aeSigma 𝓐 hA hAe)
  apply IsChartCanon.congr_data_ae hc
  filter_upwards [hAe] with ω hω
  exact ⟨(hζ ω hω).symm, rfl, eventDriver_eq hω, fun _ _ => rfl, fun _ _ => rfl⟩

end Regularize

end InteractingSLE.Sec5.CfConv
