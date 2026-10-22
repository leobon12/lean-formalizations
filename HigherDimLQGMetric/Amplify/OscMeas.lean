import HigherDimLQGMetric.Amplify.BackTransfer

/-! Measurability of the coarse oscillation failure event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Strict oscillation above a threshold is open in the space of continuous
functions, hence measurable after a measurable coarse-field map. -/
theorem amplify_measurableSet_badOsc
    {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → C(Rd d, ℝ)) (hg : Measurable g)
    (w : Rd d) (s δ : ℝ) :
    MeasurableSet {ω | ∃ x ∈ Metric.ball w (5 * s),
      ∃ y ∈ Metric.ball w (5 * s), δ < |g ω x - g ω y|} := by
  let U : Set C(Rd d, ℝ) := {f | ∃ x ∈ Metric.ball w (5 * s),
    ∃ y ∈ Metric.ball w (5 * s), δ < |f x - f y|}
  have hU : IsOpen U := by
    have heq : U = ⋃ x ∈ Metric.ball w (5 * s),
        ⋃ y ∈ Metric.ball w (5 * s),
          {f : C(Rd d, ℝ) | δ < |f x - f y|} := by
      ext f
      simp only [U, mem_ofPred_eq, mem_iUnion]
      constructor <;> rintro ⟨x, hx, y, hy, hxy⟩ <;>
        exact ⟨x, hx, y, hy, hxy⟩
    rw [heq]
    apply isOpen_biUnion
    intro x hx
    apply isOpen_biUnion
    intro y hy
    exact isOpen_lt continuous_const
      (((continuous_eval_const x).sub (continuous_eval_const y)).abs)
  exact hU.measurableSet.preimage hg

end HigherDimLQGMetric
