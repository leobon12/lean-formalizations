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
import InteractingSLE.Frozen.Spec.Chart_recenter
import InteractingSLE.Frozen.Spec.ExplState

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- Move along the original boundary from the current point to the real point `x`, recording the connector and
recentring the chart at `x` (status *onArc* `right atMark`). -/
def ExplState.moveAlong (s : ExplState) (right : Bool) (x : ℝ) (atMark : Bool) : ExplState :=
  let (pieces, arcs, retained, launches, chart, _, pt, angle, recR, recL) := s
  (pieces, arcs ++ [if right then Icc pt x else Icc x pt], retained, launches,
    chart.recenter (chart.1 x).re, .inr (.inr (.inr (.inl (right, atMark)))), x, angle,
    if right then max recR x else recR, if right then recL else min recL x)

end InteractingSLE
