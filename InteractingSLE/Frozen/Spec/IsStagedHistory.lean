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
import InteractingSLE.Frozen.Spec.Chart
import InteractingSLE.Frozen.Spec.IsChartTransport
import InteractingSLE.Frozen.Spec.IsFlowLineDriver
import InteractingSLE.Frozen.Spec.ExplSpec
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_run
import InteractingSLE.Frozen.Spec.pastSigma

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- `E` (instruction index `k ↦` driver and lifetime of the piece launched by instruction `k`) is the staged
history `spec` of the field `h`, whose boundary data is `b` (locally constant off `jumps`): whenever instruction `k`
launches an ordinary piece at angle `θ` in the chart `c` of the current domain (field `s.2.2.2.1` of the state),
then, conditionally on the retained history (`pastSigma`), that piece is the angle-`θ` flow line of the conditional
field in the current domain, read in `c` with its inherited lift: the field `h` written in `c`
(`IsChartTransport c 1 0 χ`) and the piece's driver satisfy ARCH-3's flow-line coupling, with the boundary data `b'`
(locally constant off `jumps'`) of the conditional field determined by its law (Lemmas GW1, GW2a, BW1–BW2: "launch
the same angle in the current unbounded conditional domain"; "the flow line of `h` conditional on `η|[0, τ_{j−1}]`
starting at `η(τ_{j−1})` with angle `θ_j`", §5.2, p. 136). "Conditionally on `𝒢`" is the statement under
`condExpKernel P 𝒢 ω₀` for `P`-a.e. `ω₀`. Typing and measurability conditions: the drivers are measurable, every
retained history is an event of `Ω` (`pastSigma … k ≤ mΩ`, so that `condExpKernel` conditions on exactly it), and
the recorded value at a finite positive lifetime is the continuous limit of the driver when it has one (p. 3: "a
statement at a finite `T_*` refers to its proved continuous limit"). -/
def IsStagedHistory (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (spec : ExplSpec)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  (∀ k, Measurable (E k)) ∧
  (∀ k, pastSigma κ b jumps spec E k ≤ mΩ) ∧
  (∀ k, ∀ᵐ ω ∂P, (E k ω).2 ≠ ⊤ → 0 < (E k ω).2 → ∀ c : ℝ,
      Tendsto (E k ω).1 (𝓝[<] (E k ω).2.toNNReal) (𝓝 c) → (E k ω).1 (E k ω).2.toNNReal = c) ∧
  ∀ k, ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
    (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k = some (c, θ) →
    ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsPiecewiseConstantBoundaryData b' jumps' ∧
      (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (h' ω)) ∧
      IsFlowLineDriver κ b' jumps' θ (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h'
        (fun t ω => (E k ω).1 t) (fun ω => (E k ω).2)

/-! ## G5. The light-cone families, the boundary walks and the sides of a curve -/

end InteractingSLE
