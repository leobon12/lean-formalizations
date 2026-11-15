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

/-- The first curve `γ` closed along the downward vertical ray from its seed `γ 0`:
`γ([0, ∞)) ∪ {γ 0 - i s : s ≥ 0}` (Specification p. 528, W0: "Close the first curve along its
lower vertical ray"). -/
def seedRayClosure (γ : ℝ≥0 → ℂ) : Set ℂ :=
  Set.range γ ∪ {z | z.re = (γ 0).re ∧ z.im ≤ (γ 0).im}

end InteractingSLE
