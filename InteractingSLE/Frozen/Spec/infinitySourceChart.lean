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

/-- The infinity-source chart of FD12.1 (p. 16): `R(z) = −1/z` with `L_R(z) = −2 Log z`, `0 < Im Log z < π`;
`R⁻¹ = R` as a map (FD12.2 records its compatible inverse lift). -/
def infinitySourceChart : Chart :=
  (fun z => -z⁻¹, fun z => -z⁻¹, fun z => (-2 * Complex.log z).im)

end InteractingSLE
