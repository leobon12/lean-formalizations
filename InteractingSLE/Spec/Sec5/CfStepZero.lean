/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfStepVersion

/-!
# Regular geometric chart data for the zero prefix

Packet PROVE-CFCHART2. The canonical chart clause and physical members use one
common continuous driver version and one retained filtration. Original force
coordinates are identified with geometric images before the chart conversion.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfStep

open CfConv CfGiven Exist Exist.Staged Exist.StagedLaw Restart Restart.DomainMarkov.K2
open Sec7.PocketTraversal

/-- Zero-prefix chart data with an everywhere continuous adapted driver, its
geometric force paths, infinite threshold, and physical members in the same filtration. -/
theorem exists_zero_regular_chart_members {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D)
    (hDreg : ∀ ω, IsRegularDriver (D ω)) (hDpos : ∀ᵐ ω ∂P, 0 < (D ω).2) :
    ∃ (c : BoundaryWord) (𝓐 : Filtration ℝ≥0 mΩ) (V : ℝ≥0 → Ω → ℝ),
      let xL := fun _ : Ω => flowLineXL c.fn c.jumps 0
      let xR := fun _ : Ω => flowLineXR c.fn c.jumps 0
      let ρL := flowLineRhoL (16 / κ) c.fn c.jumps 0 0
      let ρR := flowLineRhoR (16 / κ) c.fn c.jumps 0 0
      MeasurableSpace.comap (fun ω => recOf 0 (D ω)) inferInstance ≤ 𝓐 0 ∧
      (∀ ω, V 0 ω = 0) ∧ (∀ ω, Continuous fun t => V t ω) ∧ StronglyAdapted 𝓐 V ∧
      (∀ᵐ ω ∂P, ∀ t, V t ω = W t ω) ∧ (∀ᵐ ω ∂P, FCDet.thr ρL ρR V xL xR ω = ⊤) ∧
      Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 V (geomLW V xL) (geomRW V xR)
        (fun _ => ⊤) (fun ω => cfChart (recOf 0 (D ω))) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      HasSafeMembers P 𝓐 univ (fun _ => ⊤) V
        (fun ω => imgField κ (recOf 0 (D ω)) (h ω)) := by
  obtain ⟨c, 𝓕, VL, VR, B, hX, hC, hcan, hmem⟩ :=
    CfNext.exists_zero_word_chart_members hκ hcf hζ hDm hDreg hDpos
  let 𝓡 := recordFiltration (drivingFiltration P hX) (fun ω => recOf 0 (D ω))
    (measurable_recOf hDm hDreg 0)
  obtain ⟨A, hA, hAe, hAtop, hV0, hVc, hVa⟩ :=
    exists_regular_driver_event hC.1 hX hζ (𝓐 := 𝓡) (fun _ => le_sup_left)
  let V := eventDriver A W
  have he : ∀ᵐ ω ∂P, ∀ t, V t ω = W t ω := hAe.mono fun _ hω => eventDriver_eq hω
  have hg : ∀ᵐ ω ∂P,
      (∀ i t, VL i t ω = geomLW V (fun _ => flowLineXL c.fn c.jumps 0) i t ω) ∧
      ∀ j t, VR j t ω = geomRW V (fun _ => flowLineXR c.fn c.jumps 0) j t ω := by
    filter_upwards [hC.1.2.2.2.2, hζ, he] with ω hp hω hVW
    exact force_eq_geom_of_path_top hp hω (hVc ω) hVW
  have hhn : Measurable fun ω => -h ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp
        (CfRegQ.measurable_of_isCenteredCounterflowDriver hcf)).neg
  have hc₀ := CfConv.IsChartCanon.regularize_top hA hAe (fun _ _ => rfl) hhn hcan
  have hc₁ : IsChartCanon (16 / κ) (flowLineRhoL (16 / κ) c.fn c.jumps 0 0)
      (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) P (eventFiltration 𝓡 A hA) V
      (geomLW V (fun _ => flowLineXL c.fn c.jumps 0))
      (geomRW V (fun _ => flowLineXR c.fn c.jumps 0)) (fun _ => ⊤)
      (fun ω => cfChart (recOf 0 (D ω))) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) := by
    apply CfConv.IsChartCanon.congr_data_ae hc₀
    filter_upwards [hg] with ω hω
    exact ⟨rfl, rfl, fun _ => rfl, fun i t => (hω.1 i t).symm, fun j t => (hω.2 j t).symm⟩
  have hm₀ := CfResume.hasSafeMembers_of_le_aeSigma hmem
    (eventFiltration_le_aeSigma 𝓡 hA hAe)
  have hm₁ := CfResume.hasSafeMembers_congr_ae hm₀ (ae_eq_refl _) (ae_eq_refl _)
    (he.mono fun _ hω t => (hω t).symm) (ae_eq_refl _)
  refine ⟨c, eventFiltration 𝓡 A hA, V, ?_, hV0, hVc, hVa, he, ?_, ?_, hm₁⟩
  · exact le_trans (show MeasurableSpace.comap (fun ω => recOf 0 (D ω)) inferInstance ≤ 𝓡 0
      from le_sup_right) (le_eventFiltration 𝓡 A hA 0)
  · filter_upwards [hC.1.2.2.2.2, hζ, he] with ω hp hω hVW
    exact thr_eq_top_of_path_top hp hω (hVc ω) hVW
  · exact (isChartCouplingCharFunConst_iff_canon
      (fun ω => isConformal_cfChart (recOf 0 (D ω)))
      (fun ω => (hVc ω).comp continuous_real_toNNReal)).2 hc₁

end InteractingSLE.Sec5.CfStep
