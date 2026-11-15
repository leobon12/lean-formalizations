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
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling
import InteractingSLE.Frozen.Spec.upperHalfPlaneOpens
import InteractingSLE.Frozen.Spec.IsTranslateAddConst
import InteractingSLE.Frozen.Spec.flowLineNL
import InteractingSLE.Frozen.Spec.flowLineNR
import InteractingSLE.Frozen.Spec.flowLineXL
import InteractingSLE.Frozen.Spec.flowLineXR
import InteractingSLE.Frozen.Spec.flowLineRhoL
import InteractingSLE.Frozen.Spec.flowLineRhoR

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- `η`, with available lifetime `ζ`, is the angle-`θ` flow line from `x ∈ ∂ℍ` of the field `h`,
whose boundary data is `b` (locally constant off `jumps`), for `κ ∈ (0, 4)` (Specification p. 2:
"a flow line of `h` with real angle `θ` means the flow line coupled to `h + θχ`"; p. 10,
Definition: an `SLE_κ(ρ)` curve coupled with the field as in Theorem 1.1, transported by the chart
`ψ(z) = z - x`, for which `arg ψ' = 0`; p. 11, "flow line of angle `θ`"; p. 457, §3.1).

The field `h' = h(· + x) + θχ`, the flow-line force word (positions `flowLineXL`, `flowLineXR`,
weights `flowLineRhoL`, `flowLineRhoR`, whose boundary data is `b(· + x) + θχ` off its marks), a
filtration and an integrated `SLE_κ(ρ)` driving evolution `(W, V, B)` of that word with lifetime
`ζ = T_*` satisfy: `(W, V)` and `h'` form an optional hull coupling as in Theorem 1.1, and
`η - x` is almost surely the continuous generating trace of `W` on `[0, ζ]` (on every finite
interval if `ζ = ∞`). -/
def IsFlowLine (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x θ : ℝ)
    {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∃ (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (flowLineNL b jumps x) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (flowLineNR b jumps x) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ),
    (∀ ω, IsTranslateAddConst x (θ * QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
    IsOptionalHullCoupling κ (flowLineXL b jumps x) (flowLineXR b jumps x)
      (flowLineRhoL κ b jumps x θ) (flowLineRhoR κ b jumps x θ) P 𝓕 W VL VR B ζ h' ∧
    ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x)

end InteractingSLE
