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

/-- The chart after a Loewner stage driven, in the chart `c`, by `W` up to own capacity time `t`: `fwd ↦ f_t ∘ fwd`
with the centred map `f_t = fwdMap W t` (it sends the stage's tip to `0`), inverse `inv ∘ f_t⁻¹`, and lift
`arg f_t′ ∘ fwd + lift`, where `arg f_t′ = Im (logDerivFwd W t)` is the hydrodynamic branch vanishing at `t = 0`
(Theorem 1.1, p. 9; chain rule for lifts, p. 2). -/
def Chart.loewner (c : Chart) (W : ℝ → ℝ) (t : ℝ) : Chart :=
  (fun z => QuantumZipper.fwdMap W t (c.1 z),
    fun z => c.2.1 (QuantumZipper.fwdMapInv W t z),
    fun z => (QuantumZipper.logDerivFwd W t (c.1 z)).im + c.2.2 z)

end InteractingSLE
