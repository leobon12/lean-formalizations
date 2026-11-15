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

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- A chart of the current exploration domain `U = inv '' ℍ ⊆ ℍ`, as the triple `(fwd, inv, lift)`: a conformal
map `fwd : U → ℍ` sending the current seed or tip to `0` (`c.1`), its inverse `inv : ℍ → U` (`c.2.1`), and the
inherited derivative lift `lift = Im L_fwd = arg fwd′` on `U` (`c.2.2`) (Specification p. 2, "Conformal coordinate
and derivative lift", (1.4); FD12.1–FD12.2; GW1 proof, p. 618: "the exact zero lift there, inherited from its
successive own hydrodynamic maps"). This is data only; every chart used in a staged history is built literally from
the identity, the infinity-source map `R(z) = −1/z`, real translations and centred Loewner maps
`f_t = QuantumZipper.fwdMap W t`. -/
@[reducible]
def Chart : Type := (ℂ → ℂ) × (ℂ → ℂ) × (ℂ → ℝ)

end InteractingSLE
