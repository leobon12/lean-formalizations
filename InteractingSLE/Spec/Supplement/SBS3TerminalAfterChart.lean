/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3TerminalChart

/-!
# S3: the actual chart complement at a finite terminal stop

Even if a finite stopped launch completes the run, its new chart avoids
both the old explored set and the new stopped piece. Thus the chart domain
is clopen in the actual post-stop complement without a later launch.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- The post-stop chart is a clopen part of the actual explored-set
complement after a finite launch, including when the resulting state is done. -/
theorem ae_clopen_runChart_stageSet_after_finite {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E) (k : ℕ) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      min (instrTime spec k) (E k ω).2 ≠ ⊤ →
      (((ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1).dom : Set ℂ) ⊆
          H \ WalkLaw.stageSet κ b jumps spec E (k + 1) ω ∧
        IsOpen ((H \ WalkLaw.stageSet κ b jumps spec E (k + 1) ω) \
          (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.dom) := by
  filter_upwards [hR.ae_pieceRegular, WalkLaw.ae_isOpen_H_diff_stageSet hR (k + 1),
    ae_clopen_runChart_stageSet_at_launch hR k] with ω hr ho hold hl hfin
  obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hP := hr k c θ hcθ
  obtain ⟨hc, f, hf, -⟩ := GW1RestartFinal.chart_boundaryRange_run spec (fun j => E j ω) hr k
  obtain ⟨hU, hU0⟩ := hP.continuous_stoppedReal
  have hAfter : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1 =
      (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.loewner
        (fun x : ℝ => (E k ω).1
          (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (instrTime spec k) (E k ω).2)).toNNReal)
        ((min (instrTime spec k) (E k ω).2).toNNReal : ℝ) := by
    obtain ⟨-, he, -⟩ := eq_launch_of_launches spec (fun j => E j ω) hcθ
    rw [he, chart_launch _ _ _ _ _ hfin]
  have hSub := WalkSide.dom_loewner_subset hc hU hU0
    (NNReal.coe_nonneg (min (instrTime spec k) (E k ω).2).toNNReal)
  have hNew := WalkSide.disjoint_dom_loewner_tipSet hc hf hfin hP
  have hC := (GW1RestartFinal.chart_boundaryRange_run spec (fun j => E j ω) hr (k + 1)).1
  refine ⟨fun z hz => ⟨hC.dom_subset hz, ?_⟩, ?_⟩
  · rw [WalkLaw.stageSet_succ]
    intro hzA
    have hz' := hz
    change z ∈ (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.2.1.dom at hz'
    rw [hAfter] at hz'
    rcases hzA with hzOld | hzNew
    · exact ((hold hl).1 (hSub hz')).2 hzOld
    · simp only [WalkLaw.pieceSet, hl, ↓reduceIte] at hzNew
      exact Set.disjoint_left.1 hNew hz' hzNew.1
  · exact WalkSide.isOpen_diff_dom ho (WalkLeaf.mem_stageSet_of_frontier spec E ω hr (k + 1))

end InteractingSLE.Theorem14.SB.S3
