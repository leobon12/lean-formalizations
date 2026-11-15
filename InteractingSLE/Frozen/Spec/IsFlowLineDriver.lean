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
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling
import InteractingSLE.Frozen.Spec.IsTranslateAddConst
import InteractingSLE.Frozen.Spec.flowLineNL
import InteractingSLE.Frozen.Spec.flowLineNR
import InteractingSLE.Frozen.Spec.flowLineRhoL
import InteractingSLE.Frozen.Spec.flowLineRhoR
import InteractingSLE.Frozen.Spec.flowLineXL
import InteractingSLE.Frozen.Spec.flowLineXR
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- `W` (lifetime `ζ`) drives the angle-`θ` flow line from `0` of the field `h` on `ℍ`, whose boundary data is `b`
(locally constant off `jumps`) (Specification p. 2: "a flow line of `h` with real angle `θ` means the flow line
coupled to `h + θχ`"; p. 10 Definition; Theorem 1.1): ARCH-3's `IsFlowLine` at the seed `x = 0`, with the driving
function exposed instead of the trace. -/
def IsFlowLineDriver (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∃ (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ)
    (VL : Fin (flowLineNL b jumps 0) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (flowLineNR b jumps 0) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
    (∀ ω, IsTranslateAddConst 0 (θ * QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
    IsOptionalHullCoupling κ (flowLineXL b jumps 0) (flowLineXR b jumps 0)
      (flowLineRhoL κ b jumps 0 θ) (flowLineRhoR κ b jumps 0 θ) P 𝓕 W VL VR B ζ h'

end InteractingSLE
