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

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The physical points of an ordinary stage run in the chart `c` by the driver `W` through own time `s` (`s = ⊤`:
all times): the radial limits `lim_{y ↓ 0} c.inv (f_t⁻¹(i y))`, `t ≤ s`, i.e. the stage's trace points
`η(t) = lim_{y↓0} f_t⁻¹(iy)` (SLE₈ note (1.3); `QuantumZipper.trace`) read in the physical domain. A time contributes
a point exactly when the limit exists. -/
def Chart.tipSet (c : Chart) (W : ℝ≥0 → ℝ) (s : ℝ≥0∞) : Set ℂ :=
  {z | ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ s ∧
    Tendsto (fun y : ℝ => c.2.1 (QuantumZipper.fwdMapInv (fun r : ℝ => W r.toNNReal) t
      (y * Complex.I))) (𝓝[>] 0) (𝓝 z)}

end InteractingSLE
