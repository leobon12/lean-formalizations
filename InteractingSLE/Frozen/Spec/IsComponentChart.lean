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

/-- `c = (fwd, inv, lift)` is a common-lift chart `(C; x_C, y_C) → (ℍ; 0, ∞)` of a component `C` between the right
walk `R` and the left walk `L` (Lemma GW3, p. 636; Specification p. 2, "Conformal coordinate and derivative lift"):
`fwd` is a conformal bijection of `C` onto `ℍ` with inverse `inv`; `inv` has a boundary limit at every real point,
lying on `R` for a positive point (the right incoming side) and on `L` for a negative point (the left incoming side);
and `lift` is a continuous branch of `arg fwd′` on `C`. Since `fwd` preserves orientation, `0` then corresponds to
the common contact `x_C` at which the walks enter `C` (the exit of the counterflow) and `∞` to `y_C` (its entry);
such charts exist for the Jordan components of GW4 (Carathéodory) and differ by the scalings `w ↦ a w`, `a > 0`, and
by the branch of the lift (an additive constant in `2πℤ`). -/
def IsComponentChart (R L C : Set ℂ) (c : Chart) : Prop :=
  DifferentiableOn ℂ c.1 C ∧ Set.MapsTo c.1 C QuantumZipper.H ∧ Set.MapsTo c.2.1 QuantumZipper.H C ∧
    Set.InvOn c.2.1 c.1 C QuantumZipper.H ∧
    (∀ x : ℝ, ∃ p : ℂ, Tendsto c.2.1 (𝓝[QuantumZipper.H] (x : ℂ)) (𝓝 p) ∧
      (0 < x → p ∈ R) ∧ (x < 0 → p ∈ L)) ∧
    ContinuousOn c.2.2 C ∧
    ∀ z ∈ C, deriv c.1 z = (‖deriv c.1 z‖ : ℂ) * Complex.exp ((c.2.2 z : ℂ) * Complex.I)

end InteractingSLE
