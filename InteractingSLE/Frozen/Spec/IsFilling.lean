import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary


set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- `K` is the filling of `A` in `ℍ`: `ℍ \ K` is the unbounded connected component of `ℍ \ A`
(Specification p. 3, "Loewner maps, hulls and clocks": "`K_t` is the filling of its range through
`t`"; Section 2.1, p. 18). For bounded `A` there is exactly one unbounded component. -/
def IsFilling (K A : Set ℂ) : Prop :=
  (∃ z ∈ QuantumZipper.H \ K,
      connectedComponentIn (QuantumZipper.H \ A) z = QuantumZipper.H \ K) ∧
    ¬ Bornology.IsBounded (QuantumZipper.H \ K)

end InteractingSLE
