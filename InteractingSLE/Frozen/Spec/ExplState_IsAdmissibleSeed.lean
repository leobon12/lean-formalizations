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
import InteractingSLE.Frozen.Spec.sleLambda
import InteractingSLE.Frozen.Spec.ExplState

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- Both seed groups of the angle-`θ` flow at a boundary point with heights `(hL, hR)` are admissible (`> −2`):
`−(hL + θχ)/λ − 1 > −2` and `(hR + θχ)/λ − 1 > −2` (BW2.4, GW2a). -/
def ExplState.IsAdmissibleSeed (κ : ℝ) (hL hR θ : ℝ) : Prop :=
  hL + θ * QuantumZipper.chiC κ < sleLambda κ ∧ -sleLambda κ < hR + θ * QuantumZipper.chiC κ

end InteractingSLE
