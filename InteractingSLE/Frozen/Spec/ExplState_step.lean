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
import InteractingSLE.Frozen.Spec.Instr
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_contStep
import InteractingSLE.Frozen.Spec.ExplState_flowStep

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- One step of a staged history: instruction `ik.1` at index `ik.2`, with the driver family `D`. -/
def ExplState.step (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (gw2 : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (s : ExplState) (ik : Instr × ℕ) : ExplState :=
  match ik.1 with
  | .inl (θ, t) => ExplState.flowStep κ b gw2 s ik.2 (D ik.2) θ t  -- flow θ t
  | .inr (.inl pref) => ExplState.contStep κ b jumps s none pref  -- cont pref
  | .inr (.inr (v, pref)) => ExplState.contStep κ b jumps s (some v) pref  -- contTo v pref

end InteractingSLE
