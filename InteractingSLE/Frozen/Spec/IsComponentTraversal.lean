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
import InteractingSLE.Frozen.Spec.infinitySourceChart

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The counterflow driven (in the chart `R`) by `W'` traverses the component `C = inv '' ℍ` of a component chart,
from entry to exit and without erasure, as the centred counterflow driven (in the chart `R` of the component chart)
by `WC` (Theorem GW4, p. 637: "each nondegenerate matched Jordan component has its actual un-erased entry-to-exit
counterflow traversal, with continuous relative driver"; GW4 proof: `τ = T(y_C)`, `σ = T(x_C)`): there is a
continuous strictly increasing clock `T` (relative time `s ↦` ambient time `T s`) such that the counterflow does not
meet `closure C` before the time `T 0` (so `T 0` is its entry time), and for every relative time `s > 0` the ambient
trace point `η'(T s) = lim_{y↓0} R(f'⁻¹_{T s}(iy))` and the relative trace point read in `C`,
`lim_{y↓0} inv(R(f_{C,s}⁻¹(iy)))`, exist and coincide. (The relative curve tends to `x_C`; by continuity of the traces
the clock then ends at the first visit of `x_C`, or at the terminal limit when `x_C = 0`.) -/
def IsComponentTraversal (inv : ℂ → ℂ) (W' WC : ℝ≥0 → ℝ) : Prop :=
  ∃ T : ℝ≥0 → ℝ≥0, StrictMono T ∧ Continuous T ∧
    (∀ t : ℝ≥0, t < T 0 → ∀ z : ℂ,
      Tendsto (fun y : ℝ => infinitySourceChart.2.1
        (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal) t (y * Complex.I))) (𝓝[>] 0) (𝓝 z) →
      z ∉ closure (inv '' QuantumZipper.H)) ∧
    ∀ s : ℝ≥0, 0 < s → ∃ z : ℂ,
      Tendsto (fun y : ℝ => infinitySourceChart.2.1
        (QuantumZipper.fwdMapInv (fun r : ℝ => W' r.toNNReal) (T s) (y * Complex.I))) (𝓝[>] 0) (𝓝 z) ∧
      Tendsto (fun y : ℝ => inv (infinitySourceChart.2.1
        (QuantumZipper.fwdMapInv (fun r : ℝ => WC r.toNNReal) s (y * Complex.I)))) (𝓝[>] 0) (𝓝 z)

/-! ## G6. Theorem 1.4 -/

end InteractingSLE
