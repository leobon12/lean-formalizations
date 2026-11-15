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
import InteractingSLE.Frozen.Spec.ExplState

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- Follow the original boundary from the current point to the target `∞` (status *done*). -/
def ExplState.moveToEnd (s : ExplState) (right : Bool) : ExplState :=
  let (pieces, arcs, retained, launches, chart, _, pt, angle, recR, recL) := s
  (pieces, arcs ++ [if right then Ici pt else Iic pt], retained, launches, chart,
    .inr (.inr (.inr (.inr (.inl ())))), pt, angle, recR, recL)

end InteractingSLE
