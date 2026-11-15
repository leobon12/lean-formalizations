/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfNextZeroChart

/-!
# Zero-prefix chart and locality clauses in one retained filtration

Packet PROVE-CFCHART2. This assembles the original word coupling, the reverse
chart clause and physical member locality, with the actual zero-prefix record retained.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfNext

open CfConv CfChart CfGiven Exist Exist.Staged Exist.StagedLaw Restart Restart.DomainMarkov.K2

/-- The original zero-prefix counterflow has both canonical chart and member clauses
in its driving filtration enlarged by the literal record. The original force paths are retained. -/
theorem exists_zero_word_chart_members {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hDm : Measurable D)
    (hDreg : ∀ ω, IsRegularDriver (D ω)) (hDpos : ∀ᵐ ω ∂P, 0 < (D ω).2) :
    ∃ (c : BoundaryWord) (𝓕 : Filtration ℝ≥0 mΩ)
      (VL : Fin (flowLineNL c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ)
      (VR : Fin (flowLineNR c.fn c.jumps 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (hX : IsMeasurableKilledDriving W VL VR ζ),
      let 𝓐 := recordFiltration (drivingFiltration P hX) (fun ω => recOf 0 (D ω))
        (measurable_recOf hDm hDreg 0)
      IsOptionalHullCoupling (16 / κ) (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
        (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0)
        P 𝓕 W VL VR B ζ (fun ω => imgField κ (recOf 0 (D ω)) (h ω)) ∧
      IsChartCanon (16 / κ) (flowLineRhoL (16 / κ) c.fn c.jumps 0 0)
        (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) P 𝓐 W VL VR (fun _ => ⊤)
        (fun ω => cfChart (recOf 0 (D ω))) (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω) ∧
      HasSafeMembers P 𝓐 univ (fun _ => ⊤) W
        (fun ω => imgField κ (recOf 0 (D ω)) (h ω)) := by
  obtain ⟨c, 𝓕, VL, VR, B, hX, hC, hmem⟩ := exists_zero_word_members hκ hcf hζ hDm hDreg hDpos
  have ht : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC κ)) (-chiC κ)
      (h ω) (imgField κ (recOf 0 (D ω)) (h ω)) := by
    intro ω
    have hi := isChartTransport_imgField κ (recOf 0 (D ω)) (h ω)
    rw [CfResume.recField_recOf_zero, Sec4.chiC_sixteen_div hκ] at hi
    exact hi
  have hcan := isChartCanon_zero_record D (isChartCanon_source_of_optional_top hC hX hζ ht)
  have hhn : Measurable fun ω => -h ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ =>
      ((LQGMetric.measurable_distOn_apply φ).comp
        (CfRegQ.measurable_of_isCenteredCounterflowDriver hcf)).neg
  refine ⟨c, 𝓕, VL, VR, B, hX, hC, ?_, hmem⟩
  apply CfChart.IsChartCanon.of_le_aeSigma hcan hhn (fun _ => le_sup_left)
  intro t
  exact sup_le (le_aeSigma _ _) (CfResume.recordSigma_zero_le_aeSigma hDreg hDpos _ t)

end InteractingSLE.Sec5.CfNext
