/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTail
import InteractingSLE.Spec.Restart.MarkovChart

/-!
# The actual added set in an old pocket chart

PROVE-POCKET-SIDEIN. The added set is the complement of the current
physical domain pulled back by the old inverse, normalized to the empty
set off the candidate event. Its regularity and the surviving collar are
geometric conclusions, independent of the conditional increment field law.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

open Classical in
/-- The actual increment set in the old coordinate, empty off its own
candidate event. -/
def oldChartAddedSet {Ω : Type*} (M : Set Ω) (old current : Ω → Chart) (ω : Ω) : Set ℂ :=
  if ω ∈ M then H \ Restart.MarkovChart.chartPre (old ω) (current ω).dom else ∅

/-- On its event the complement is precisely the current domain in the
old coordinate. -/
theorem compl_oldChartAddedSet {Ω : Type*} {M : Set Ω} {old current : Ω → Chart}
    {ω : Ω} (hω : ω ∈ M) :
    H \ oldChartAddedSet M old current ω =
      Restart.MarkovChart.chartPre (old ω) (current ω).dom := by
  rw [oldChartAddedSet, ite_eq_left hω]
  exact sdiff_sdiff_cancel_left (Restart.MarkovChart.chartPre_subset_H _ _)

/-- Regularity needs only conformality of the old chart on its event;
the current chart domain is already open. -/
theorem oldChartAddedSet_regular {Ω : Type*} {M : Set Ω} {old current : Ω → Chart}
    (hOld : ∀ ω ∈ M, (old ω).IsConformal) (ω : Ω) :
    oldChartAddedSet M old current ω ⊆ H ∧ IsOpen (H \ oldChartAddedSet M old current ω) := by
  by_cases hω : ω ∈ M
  · refine ⟨?_, ?_⟩
    · rw [oldChartAddedSet, ite_eq_left hω]
      exact sdiff_subset
    · rw [compl_oldChartAddedSet hω]
      exact Restart.MarkovChart.isOpen_chartPre (hOld ω hω) (current ω).dom.isOpen
  · rw [oldChartAddedSet, ite_eq_right hω, sdiff_empty]
    exact ⟨empty_subset _, QuantumZipper.isOpen_H⟩

/-- The physical unfilled collar excludes the actual added set. -/
theorem oldChartAddedSet_disjoint_of_inverse_collar {Ω : Type*} {M : Set Ω}
    {old current : Ω → Chart} {ω : Ω} (hω : ω ∈ M) {x r : ℝ}
    (hCollar : (old ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (current ω).dom) :
    Disjoint (H ∩ ball (x : ℂ) r) (oldChartAddedSet M old current ω) := by
  rw [oldChartAddedSet, ite_eq_left hω]
  refine disjoint_left.2 fun z hz hzAdded => hzAdded.2 ?_
  exact ⟨hz.1, hCollar (mem_image_of_mem (old ω).2.1 hz)⟩

end InteractingSLE.Sec7.PocketStopSide
