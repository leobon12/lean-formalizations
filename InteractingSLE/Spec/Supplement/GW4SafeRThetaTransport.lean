/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4CLocChart
import InteractingSLE.Spec.Sec7.SideC12Physical

/-! # GW4: the physical harmonic mean through a component chart

The actual chosen representative of a transported harmonic distribution
obeys the chart formula on the entire preimage domain. This identifies
the representative used by the Gaussian union kernel, with its inherited
lift, before the source inversion and centering of SideC12 are applied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart.MarkovChart Sec7.Aux119Heights

/-- The canonical harmonic representative of an actual component chart
transport has exactly the transported value and inherited lift. -/
theorem harmRep_component_transport {R L C : Set ℂ} {c : Chart}
    (hch : IsComponentChart R L C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    {U : Set ℂ} (hUo : IsOpen U) {M : DistOn upperHalfPlaneOpens}
    (hM : IsHarmonicDistOn M U) (a k : ℝ) :
    let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
    EqOn (harmRep (Chart.chartTransport hc 1 a k M) (chartPre c U))
      (fun z => harmRep M U (c.2.1 z) + a + k * c.2.2 (c.2.1 z)) (chartPre c U) := by
  let hc := GW3Law.isConformal_of_isComponentChart hch hCo hCH
  have hD : (c.dom : Set ℂ) = C := CLoc.coe_dom_of_isComponentChart hch hCo hCH
  have hlc : ContinuousOn c.2.2 c.dom := hD ▸ hch.2.2.2.2.2.1
  have hlh : InnerProductSpace.HarmonicOnNhd c.2.2 c.dom :=
    hD ▸ CLoc.harmonicOnNhd_lift_of_isComponentChart hch hCo hCH
  have hO : IsOpen (chartPre c U) := isOpen_chartPre hc hUo
  have hOH : chartPre c U ⊆ H := chartPre_subset_H _ _
  have hMI : IsHarmonicDistOn M (c.2.1 '' chartPre c U) := by
    rw [image_chartPre hc]
    exact IsHarmonicDistOn.mono hM inter_subset_left
  have hT := Sec7.Lemma72C.isHarmonicDistOn_chartTransport hc hlc hlh hO hOH hMI a k
  obtain ⟨hv, hrep⟩ := harmRep_spec hM
  obtain ⟨hvT, hrepT⟩ := harmRep_spec hT
  have hv' : InnerProductSpace.HarmonicOnNhd (fun z => harmRep M U (c.2.1 z)) (chartPre c U) := by
    intro z hz
    exact QuantumZipper.Thm18Asm.LWFar.pocket_harmonicAt_comp
      (hc.1.analyticAt (QuantumZipper.isOpen_H.mem_nhds hz.1)) (hv _ hz.2)
  have hl' : InnerProductSpace.HarmonicOnNhd (fun z => c.2.2 (c.2.1 z)) H :=
    LQGMetric.harmonicOnNhd_comp_holo c.dom.isOpen QuantumZipper.isOpen_H hlh hc.1
      (fun z hz => hc.inv_mem_dom hz)
  have hV : InnerProductSpace.HarmonicOnNhd
      (fun z => harmRep M U (c.2.1 z) + a + k * c.2.2 (c.2.1 z)) (chartPre c U) := by
    intro z hz
    exact ((hv' z hz).add (InnerProductSpace.harmonicAt_const a)).add
      ((hl' z hz.1).const_smul (c := k))
  refine Sec6.eqOn_of_integral_mul_eq hO hOH hvT hV fun φ hφ => ?_
  have hℓ := Chart.locallyIntegrableOn_of_continuousOn (hc.continuousOn_lift_inv hlc)
  have hvC : ContinuousOn (fun z => harmRep M U (c.2.1 z)) (chartPre c U) := hv'.continuousOn
  have hlC : ContinuousOn (fun z => c.2.2 (c.2.1 z)) (chartPre c U) :=
    (hc.continuousOn_lift_inv hlc).mono hOH
  have hiV := Coupling.MartMeans2.integrable_mul_test_of_continuousOn hvC φ hφ
  have hiL := Coupling.MartMeans2.integrable_mul_test_of_continuousOn hlC φ hφ
  have hi0 : Integrable (fun z => φ z) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  rw [← hrepT φ hφ, Chart.chartTransport_apply hc hℓ, one_mul,
    hrep _ (tsupport_pushTest_subset_of_chartPre hc hφ), Chart.integral_mul_pushTest]
  have he : (fun z => (harmRep M U (c.2.1 z) + a + k * c.2.2 (c.2.1 z)) * φ z) =
      fun z => (harmRep M U (c.2.1 z) * φ z + a * φ z) +
        k * (c.2.2 (c.2.1 z) * φ z) := by funext z; ring
  have hAdd := integral_add (hiV.add (hi0.const_mul a)) (hiL.const_mul k)
  have hAdd' := integral_add hiV (hi0.const_mul a)
  simp only [Pi.add_apply] at hAdd hAdd'
  rw [he, hAdd, hAdd', integral_const_mul, integral_const_mul]

end InteractingSLE.Theorem14.GW4Fix
