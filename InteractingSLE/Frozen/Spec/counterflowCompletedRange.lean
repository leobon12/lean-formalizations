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
import InteractingSLE.Frozen.Spec.Chart_tipSet
import InteractingSLE.Frozen.Spec.infinitySourceChart

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The completed range of the centred counterflow driven (in the chart `R`) by `W`, as a subset of `ℂ`: its
physical points `R(γ(t))`, `t ≥ 0`, together with its terminal point `0` (Theorem 1.4: "the entire completed range
of `η'`"). The initial point `∞` is not a point of `ℂ`; every set compared with this one omits `∞` as well, so
equality here is equality of the completed ranges in the Riemann sphere. -/
def counterflowCompletedRange (W : ℝ≥0 → ℝ) : Set ℂ :=
  infinitySourceChart.tipSet W ⊤ ∪ {0}

/-! ## G3. Prescribed finite staged histories (GW1, GW2, GW2a) -/

end InteractingSLE
