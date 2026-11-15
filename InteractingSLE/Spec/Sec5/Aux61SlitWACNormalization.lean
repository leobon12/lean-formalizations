/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWACTarget

/-! # The exact normalization clauses needed by `ChoiceInputs`

The normalized R1 construction supplies all domain geometry and both
collars. For the literal weaker selector, only its target mark, limits
and inherited lift are additional conditions. These conditional adapters
do not assert that the weaker choice retains that certificate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAC
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61Asm2 LawUnique

/-- Domain geometry, including both physical collars, transfers to any
chart on the same domain once its own normalization clauses are given. -/
theorem sourceChartGeometry_of_same_domain {W : ℝ → ℝ} {η : ℝ → ℂ}
    {K : Set ℂ} {r : ℝ≥0} {c d : Chart} (hg : SourceChartGeometry W η K r c)
    (hd : d.dom = c.dom)
    (hinfty : Tendsto (fun z : ℂ => ‖d.1 (z + 1)‖) (𝓝[H] 0) atTop)
    (hlift : ∀ z ∈ (d.dom : Set ℂ),
      d.2.2 z = (physicalRestartLog (stripTargetHull d.dom) z).im)
    (hcurrent : Tendsto (fun z => d.1 (fwdMapInv W r z)) (𝓝[H] 0) (𝓝 0)) :
    SourceChartGeometry W η K r d where
  start_pos := hg.start_pos
  retained := hd ▸ hg.retained
  simply := hd ▸ hg.simply
  target := hd ▸ hg.target
  infty := hinfty
  lift := hlift
  collar := hd ▸ hg.collar
  current := hcurrent

universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The exact `ChoiceInputs.chart_geometry` field from the four retained
normalization clauses. In particular no separate collar, simple
connectedness, domain or fresh-continuation hypothesis remains. -/
theorem chart_geometry_of_normalization (hsel : ∀ i, MeasurableSet (C.selected i))
    (htarget : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → (1 : ℂ) ∈ closure
      ((sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ))
    (hinfty : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → Tendsto
      (fun z : ℂ => ‖(sourceChart C.fam (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p).1 (z + 1)‖) (𝓝[H] 0) atTop)
    (hlift : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → ∀ z ∈
      (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom,
      (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.2 z =
        (physicalRestartLog (stripTargetHull
          (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom) z).im)
    (hcurrent : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → Tendsto
      (fun z => (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).1
        (fwdMapInv (fun t : ℝ => S.own.W t.toNNReal p.1) (rationalTime (C.toR1Restart.q i)) z))
      (𝓝[H] 0) (𝓝 0)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (GlueCond.cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
  have R := Aux61SlitWZ.readers C hsel
  intro i
  filter_upwards [R.ae_geometry C.hasChart i, ae_domain_eq_normalized_of_target C hsel htarget i,
    hinfty i, hlift i, hcurrent i] with p hg hd hi hl hc he
  exact sourceChartGeometry_of_same_domain (hg he) (hd he) (hi he) (hl he) (hc he)

/-- The same exact field from normalization stated wholly on selected
initial records. The current map is read only through the retained own
driver; its equality with the physical inverse is already proved. -/
theorem chart_geometry_of_record_normalization (hsel : ∀ i, MeasurableSet (C.selected i))
    (htarget : ∀ i y, y ∈ C.toR1Restart.selected i →
      (1 : ℂ) ∈ closure ((C.toR1Restart.chart C.hasChart i y).dom : Set ℂ))
    (hinfty : ∀ i y, y ∈ C.toR1Restart.selected i → Tendsto
      (fun z : ℂ => ‖(C.toR1Restart.chart C.hasChart i y).1 (z + 1)‖) (𝓝[H] 0) atTop)
    (hlift : ∀ i y, y ∈ C.toR1Restart.selected i → ∀ z ∈ (C.toR1Restart.chart C.hasChart i y).dom,
      (C.toR1Restart.chart C.hasChart i y).2.2 z =
        (physicalRestartLog (stripTargetHull (C.toR1Restart.chart C.hasChart i y).dom) z).im)
    (hcurrent : ∀ i y, y ∈ C.toR1Restart.selected i → Tendsto
      ((C.toR1Restart.chart C.hasChart i y).1 ∘
        (ownHistoryChart (C.toR1Restart.U i) (C.toR1Restart.r i) y).2.1) (𝓝[H] 0) (𝓝 0)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (GlueCond.cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
  apply chart_geometry_of_normalization C hsel
  · exact fun i => Eventually.of_forall fun p he => htarget i _ he
  · exact fun i => Eventually.of_forall fun p he => hinfty i _ he
  · exact fun i => Eventually.of_forall fun p he => hlift i _ he
  · have R := Aux61SlitWZ.readers C hsel
    intro i
    filter_upwards [R.ae_inverse_eq C.hasChart] with p hp he
    exact (hcurrent i _ he).congr'
      ((show ∀ᶠ z : ℂ in 𝓝[H] 0, z ∈ H from self_mem_nhdsWithin).mono fun z hz => congrArg
        (C.toR1Restart.chart C.hasChart i
          (sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)).1
        (hp i he hz))

end InteractingSLE.Sec5.Aux61SlitWAC
