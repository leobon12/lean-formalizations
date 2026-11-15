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

/-- `γ'` is a continuous injective proper extension in the closed upper half-plane, from the
seed to `∞`, of the prefix `γ|[0, a]` (Specification p. 528, W0). The prefix keeps its own
parametrization on `[0, a]` (W0 reparametrizes it linearly; the image and order are the same). -/
def IsProperCompletion (γ : ℝ≥0 → ℂ) (a : ℝ≥0) (γ' : ℝ≥0 → ℂ) : Prop :=
  Continuous γ' ∧ Function.Injective γ' ∧ (∀ t, 0 ≤ (γ' t).im) ∧
    Tendsto (fun t => ‖γ' t‖) atTop atTop ∧ ∀ t ≤ a, γ' t = γ t

end InteractingSLE
