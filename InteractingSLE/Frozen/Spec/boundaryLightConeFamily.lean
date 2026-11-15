import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import InteractingSLE.Frozen.Spec.ExplSpec
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_physSet
import InteractingSLE.Frozen.Spec.scheduleProgram
import InteractingSLE.Frozen.Spec.IsSchedule
import InteractingSLE.Frozen.Spec.lowerArcRoots

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The countable boundary-continued light-cone family of GW2 (p. 621), as a set (before closure), for boundary
data `b` (locally constant off `jumps`): all available finite `Θ`-schedules from `0` with times in `Q`, each
retained through its actual available portion; and, for every root `v` of `lowerArcRoots`, the forced
original-boundary arc `[0, v]` together with all available finite `Θ`-schedules from `v` with times in `Q`.
`D spec` is the driver family of the history `spec`. -/
def boundaryLightConeFamily (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (Θ : Set ℝ) (Q : Set ℝ≥0)
    (D : ExplSpec → ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Set ℂ :=
  (⋃ l ∈ {l | IsSchedule Θ Q l},
      ExplState.physSet κ b jumps ⟨0, true, scheduleProgram 0 l⟩ (D ⟨0, true, scheduleProgram 0 l⟩)) ∪
    ⋃ v ∈ lowerArcRoots κ b jumps,
      (((↑) : ℝ → ℂ) '' Icc 0 v ∪
        ⋃ l ∈ {l | IsSchedule Θ Q l},
          ExplState.physSet κ b jumps ⟨v, true, scheduleProgram 0 l⟩ (D ⟨v, true, scheduleProgram 0 l⟩))

end InteractingSLE
