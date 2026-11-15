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
import InteractingSLE.Frozen.Spec.Instr

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- A prescribed finite boundary-continued staged history of GW2a (p. 623): every ordinary angle (every *flow*
instruction `.inl (θ, t)`) lies in `[−π/2, π/2]`. -/
def IsBoundaryContinuedProgram (p : List Instr) : Prop :=
  ∀ θ t, (Sum.inl (θ, t) : Instr) ∈ p → θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)

end InteractingSLE
