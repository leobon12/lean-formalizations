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

/-- The physical set of the history `spec`: its root, the physical points of its ordinary pieces (`s.1`), and its
recorded original-boundary connectors (`s.2.1`), for the final state `s`. -/
def ExplState.physSet (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : Set ℂ :=
  let s := ExplState.run κ b jumps spec D spec.2.2.length
  {(spec.1 : ℂ)} ∪ (⋃ p ∈ s.1, p.1.tipSet p.2.1 p.2.2) ∪ ⋃ a ∈ s.2.1, ((↑) : ℝ → ℂ) '' a

/-! ## G4. Staged histories of the field: every ordinary piece is a conditional flow line -/

end InteractingSLE
