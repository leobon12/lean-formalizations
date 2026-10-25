import SupercriticalLQGUniqueness.B2.PfeWeyl.R68S1TCircleSqueeze
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3XUpperFamily

 

set_option autoImplicit false
noncomputable section

open Set Filter Topology

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

theorem upperShiftFamily_countableUpperShifts :
    CountableUpperShifts upperShiftFamily := by
  intro f M hM
  have hchoice : ∀ j : ℕ, ∃ i : ℕ,
      (∀ z, f z ≤ upperShiftFamily i z) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) j,
        upperShiftFamily i z ≤ f z + 1 / ((j : ℝ) + 1) := by
    intro j
    exact upperShiftFamily_orderDense f M hM _ (isCompact_closedBall _ _)
      _ (by positivity)
  refine ⟨fun j => Classical.choose (hchoice j), ?_, ?_⟩
  · intro j z
    exact (Classical.choose_spec (hchoice j)).1 z
  · intro j z hz
    exact (Classical.choose_spec (hchoice j)).2 z hz

end SupercriticalLQGUniqueness.B2.PfeWeyl
