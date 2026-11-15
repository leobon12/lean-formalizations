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
import InteractingSLE.Frozen.Spec.ExplState_init
import InteractingSLE.Frozen.Spec.ExplState_step

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The state after the first `k` instructions of the history `spec = (root, gw2, prog)`, with drivers `D`. -/
def ExplState.run (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (k : ℕ) : ExplState :=
  (spec.2.2.zipIdx.take k).foldl (ExplState.step κ b jumps spec.2.1 D) (ExplState.init spec.1)

end InteractingSLE
