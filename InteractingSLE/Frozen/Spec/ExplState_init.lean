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
import InteractingSLE.Frozen.Spec.Chart
import InteractingSLE.Frozen.Spec.Chart_id
import InteractingSLE.Frozen.Spec.Chart_recenter
import InteractingSLE.Frozen.Spec.ExplState

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The initial state at the root `x₀`: no pieces, no connectors, chart `z ↦ z − x₀` (lift `0`), status *root*,
current point and records `x₀`, angle `0`. -/
def ExplState.init (x₀ : ℝ) : ExplState :=
  ([], [], fun _ => (fun _ => 0, 0, false), fun _ => none, Chart.id.recenter x₀, .inl (), x₀, 0, x₀, x₀)

end InteractingSLE
