/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3MarkedMean
import InteractingSLE.Spec.Supplement.SB2JK2
import InteractingSLE.Spec.Supplement.WalkLeafChart
import InteractingSLE.Spec.Supplement.WalkSideDom
import InteractingSLE.Spec.Supplement.WalkIntRunChronCarrier

/-!
# S3: retained chart data and the actual stage complement

Reuse the measurable version of the run chart and the existing frontier
and disjointness theorems. The domain is a clopen part of the explored-set
complement at a launch; it need not exhaust that complement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- The existing measurable random-chart interface supplies exactly the
retained chart observations used by the marked mean identification. -/
theorem RetainedChartData.of_isMeasChart {Ω : Type u} {𝒢 : MeasurableSpace Ω}
    {c : Ω → Chart} (hc : WalkInf.IsMeasChart 𝒢 c) : RetainedChartData 𝒢 c :=
  ⟨hc.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2, hc.2.2.1⟩

/-- The actual retained-record version of a staged chart has all required
measurable observations and its inherited harmonic lift. -/
theorem retainedChartData_verChart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    RetainedChartData (pastSigma κ b jumps spec E k) (WalkInf.verChart κ b jumps spec E k) :=
  RetainedChartData.of_isMeasChart (WalkInf.isMeasChart_verChart hb hEm hreg k)

/-- At an actual launch, the current chart domain is a clopen part of the
complement of the actual explored set. Only R51 piece regularity is used. -/
theorem ae_clopen_runChart_stageSet_at_launch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      (((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1).dom : Set ℂ) ⊆
          H \ WalkLaw.stageSet κ b jumps spec E k ω ∧
        IsOpen ((H \ WalkLaw.stageSet κ b jumps spec E k ω) \
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom) := by
  filter_upwards [hR.ae_pieceRegular, WalkLaw.ae_isOpen_H_diff_stageSet hR k] with ω hr ho hl
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd := WalkIntRunChron.not_done_of_launch _ _ hcθ
  have hdis := (WalkSide.disjoint_dom_or_done spec (fun j => E j ω) hr k).resolve_left hnd
  have hconf := (GW1RestartFinal.chart_boundaryRange_run spec (fun j => E j ω) hr k).1
  refine ⟨fun z hz => ⟨hconf.dom_subset hz, fun hzA => Set.disjoint_left.1 hdis hz hzA.1⟩, ?_⟩
  exact WalkSide.isOpen_diff_dom ho (WalkLeaf.mem_stageSet_of_frontier spec E ω hr k)

end InteractingSLE.Theorem14.SB.S3
