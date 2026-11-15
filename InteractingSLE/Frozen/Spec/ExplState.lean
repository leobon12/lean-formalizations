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
import InteractingSLE.Frozen.Spec.ExplStatus

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The state of a staged history after finitely many instructions, as the 10-tuple
`(pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL)`:
* `pieces` (`s.1`): the ordinary pieces, each as (chart at launch, driver stopped at its stop time, stop time);
* `arcs` (`s.2.1`): the recorded original-boundary connectors;
* `retained` (`s.2.2.1`): the retained datum of the piece launched by instruction `k` (stopped driver, stop time,
  whether it ended by its continuation threshold); `(0, 0, false)` if none;
* `launches` (`s.2.2.2.1`): the chart and angle at which instruction `k` launched an ordinary piece, if it did;
* `chart`: the chart of the current unbounded domain, centred at the current point;
* `status`: the current status;
* `pt`: the current physical point on `ℝ` (meaningful at the root, a threshold, or a connector);
* `angle`: the angle of the last ordinary piece run;
* `recR`, `recL`: the largest and the smallest original real point reached so far. -/
@[reducible]
def ExplState : Type :=
  List (Chart × (ℝ≥0 → ℝ) × ℝ≥0∞) × List (Set ℝ) × (ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ × Bool) ×
    (ℕ → Option (Chart × ℝ)) × Chart × ExplStatus × ℝ × ℝ × ℝ × ℝ

end InteractingSLE
