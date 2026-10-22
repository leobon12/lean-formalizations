import HigherDimLQGMetric.Sec8.Events
import HigherDimLQGMetric.Sphere.Proc

/-!
# Borel parts of the Section 8 favorable event

The comparison condition (C1) is a measurable evaluation of two metric
assignments and the sphere average. A path visiting an open ball is detected
at one of a fixed countable dense set of times, giving (C3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric Topology unitInterval
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A continuous path visits an open ball at some time exactly when it does
so at one of the fixed dense sequence of times. -/
theorem measurableSet_sec8_path_hits_ball (z : Rd d) (r : ℝ) :
    MeasurableSet {η : C(unitInterval, Rd d) | ∃ t : unitInterval, η t ∈ ball z r} := by
  have heq : {η : C(unitInterval, Rd d) | ∃ t : unitInterval, η t ∈ ball z r} =
      ⋃ n : ℕ, {η | η (TopologicalSpace.denseSeq unitInterval n) ∈ ball z r} := by
    ext η
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      have hU : IsOpen (η ⁻¹' ball z r) := isOpen_ball.preimage η.continuous
      exact (TopologicalSpace.denseRange_denseSeq unitInterval).exists_mem_open hU ⟨t, ht⟩
    · rintro ⟨n, hn⟩
      exact ⟨TopologicalSpace.denseSeq unitInterval n, hn⟩
  rw [heq]
  exact MeasurableSet.iUnion fun n =>
    (continuous_eval_const (TopologicalSpace.denseSeq unitInterval n)).measurable isOpen_ball.measurableSet

/-- (C1) is Borel whenever the metric assignments are Borel. -/
theorem measurableSet_sec8C1 {D Dt : DistRd d → ContMetric d}
    (hD : Measurable D) (hDt : Measurable Dt)
    (ξ Q Cstar q R : ℝ) (x y : Rd d) :
    MeasurableSet {g : DistRd d | sec8C1 D Dt ξ Q Cstar q R x y g} := by
  have hDe : Measurable fun g : DistRd d => (D g).1 (x, y) :=
    (continuous_eval_const (x, y)).measurable.comp (measurable_subtype_coe.comp hD)
  have hDte : Measurable fun g : DistRd d => (Dt g).1 (x, y) :=
    (continuous_eval_const (x, y)).measurable.comp (measurable_subtype_coe.comp hDt)
  have hS : Measurable fun g : DistRd d => macroS ξ Q g R := by
    exact measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul (measurable_sphereAvg_left (8 * R) 0)))
  exact measurableSet_le ((measurable_const.mul hDe).sub (measurable_const.mul hS)) hDte

/-- (C3) is Borel: each member of the finite label set is tested by a
countable union of path evaluations. -/
theorem measurableSet_sec8C3 {D : DistRd d → ContMetric d} (hD : Measurable D)
    (x y : Rd d) (r : ℝ) (Z : Finset (Rd d × ℕ)) :
    MeasurableSet {g : DistRd d | sec8C3 D x y r Z g} := by
  let selMap : DistRd d → C(unitInterval, Rd d) :=
    fun g => sec8Sel x y (D g).1
  have hsel : Measurable selMap :=
    (measurable_sec8Sel x y).comp (measurable_subtype_coe.comp hD)
  have heq : {g : DistRd d | sec8C3 D x y r Z g} =
      ⋂ q : {q : Rd d × ℕ // q ∈ Z},
        {g | ∃ t : unitInterval, selMap g t ∈ ball q.1.1 r} := by
    ext g
    simp only [sec8C3, mem_ofPred_eq, mem_iInter]
    constructor
    · intro hg q
      exact hg q.1 q.2
    · intro hg q hq
      exact hg ⟨q, hq⟩
  rw [heq]
  exact MeasurableSet.iInter fun q =>
    hsel (measurableSet_sec8_path_hits_ball q.1.1 r)

end HigherDimLQGMetric
