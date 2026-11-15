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
import InteractingSLE.Frozen.Spec.ExplSpec
import InteractingSLE.Frozen.Spec.ExplState
import InteractingSLE.Frozen.Spec.ExplState_run

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The ordinary part of the history `spec`: the physical points of its ordinary pieces (field `s.1` of the final
state `s`), without its root and its original-boundary connectors (Lemma GW3, p. 636: "ordinary extremal piece"
versus "original-real connector"). -/
def ExplState.ordinarySet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Set ℂ :=
  ⋃ p ∈ (ExplState.run κ b jumps spec D spec.2.2.length).1, p.1.tipSet p.2.1 p.2.2

end InteractingSLE
