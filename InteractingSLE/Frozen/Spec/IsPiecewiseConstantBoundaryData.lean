import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- Finite piecewise-constant boundary data on `∂ℍ = ℝ` (Specification p. 5, Theorem 1.5: "`h`
has finite piecewise-constant boundary data on `ℍ`"; p. 457, §3.1: "bounded, piecewise constant
boundary values having finitely many jumps"): the function `b : ℝ → ℝ` is locally constant off the
finite set `jumps`. The values of `b` at the points of `jumps` are irrelevant (they do not change
the harmonic extension and are never read); only one-sided limits are used. `jumps` may contain
points where `b` does not actually jump. -/
def IsPiecewiseConstantBoundaryData (b : ℝ → ℝ) (jumps : Finset ℝ) : Prop :=
  ∀ y ∉ jumps, ∀ᶠ z in 𝓝 y, b z = b y

end InteractingSLE
