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

/-- `φ` is a common active chart of `D` centered at the boundary point `p` (Specification
p. 458, Theorem 7.9A(2): "`φ₀ : D₀ → ℍ` send the common active prime end to `0` and the target
to `∞`"; p. 290, Lemma 7.8: "`φ : D → ℍ` fix infinity"): a conformal bijection of `D` onto `ℍ`,
with `φ(z) → 0` as `z → p` in `D` and `φ(z) → ∞` as `z → ∞` in `D`. Two such charts differ by a
positive scaling. -/
def IsActiveChart (D : Set ℂ) (p : ℂ) (φ : ℂ → ℂ) : Prop :=
  Set.BijOn φ D QuantumZipper.H ∧ DifferentiableOn ℂ φ D ∧ Tendsto φ (𝓝[D] p) (𝓝 0) ∧
    Tendsto φ (Bornology.cobounded ℂ ⊓ 𝓟 D) (Bornology.cobounded ℂ)

end InteractingSLE
