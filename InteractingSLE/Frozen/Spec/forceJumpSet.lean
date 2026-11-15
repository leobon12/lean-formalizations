import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import QuantumZipper.Loewner.Forward
import QuantumZipper.GFF.Kernels
import LQGMetric.Field.ZeroBoundary


set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

/-- The finite set of possible jump points of `forceBoundaryData`: `0` and the force points. -/
def forceJumpSet {nL nR : ℕ} (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) : Set ℝ :=
  insert 0 (Set.range vL ∪ Set.range vR)

end InteractingSLE
