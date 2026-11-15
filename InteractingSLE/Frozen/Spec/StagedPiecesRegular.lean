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
import InteractingSLE.Frozen.Spec.ExplSpec
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_run
import InteractingSLE.Frozen.Spec.IsGeneratingTrace

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- **The launched pieces of the staged history `E` are continuous curves almost surely** (ruling R51; the source's
pieces are actual curves, §5.2, p. 136, and Lemmas GW1, GW2a, pp. 618–623). `P`-almost surely, for every instruction
`k` of the program that is an ordinary piece `(θ, t)` and launches a piece (field `s.2.2.2.1` of the state after the
instructions `0, …, k`), the piece's driver `w = (E k ω).1` run to its stop `S = min t ζ` (`ζ = (E k ω).2`, its
lifetime) starts at `0`, is continuous on `[0, S]` (on `[0, ∞)` when `S = ∞`), and has a continuous generating trace on
`[0, S]` (`IsGeneratingTrace`), which tends to infinity when `S = ∞`. -/
def StagedPiecesRegular (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂P, ∀ (k : ℕ) (θ : ℝ) (t : ℝ≥0∞) (c : Chart),
    spec.2.2[k]? = some (Sum.inl (θ, t)) →
    (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ) →
    (E k ω).1 0 = 0 ∧ ContinuousOn (E k ω).1 {s | (s : ℝ≥0∞) ≤ min t (E k ω).2} ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E k ω).1 (min t (E k ω).2) η ∧
        (min t (E k ω).2 = ⊤ → Tendsto (fun s => ‖η s‖) atTop atTop)

end InteractingSLE
