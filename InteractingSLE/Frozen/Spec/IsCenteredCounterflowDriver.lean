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
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.infinitySourceChart
import InteractingSLE.Frozen.Spec.IsChartTransport
import InteractingSLE.Frozen.Spec.IsFlowLineDriver

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- `W` (lifetime `ζ`) drives the centred counterflow `η' = CF_d(h)` of the flow field `h` on `ℍ`, from `∞` to `0`,
with the infinity-source derivative lift FD12.1–FD12.2 (Theorem 1.4, p. 4; FD11.1 `CF_d(h) = CF_lit(h + πχ)`,
coupled to `F_d(h) = −h − πχ`; FD12.5). In the chart `R`, the curve `R(η')` from `0` to `∞` is the Theorem 1.1
curve, parameter `κ' = 16/κ`, of the parameter field `F_d(h)^R = −h ∘ R + πχ − 2χ arg w`; the boundary data `b'`
(locally constant off `jumps'`) of that field is determined by its law. The physical counterflow is `η' = R(γ)` for
the trace `γ` of `W`. -/
def IsCenteredCounterflowDriver (κ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b' jumps' ∧
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) ∧
    IsFlowLineDriver (16 / κ) b' jumps' 0 P h' W ζ

end InteractingSLE
