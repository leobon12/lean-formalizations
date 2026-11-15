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

/-- The ordering conditions of an ordered finite force word (Specification p. 3, "Ordered force words and
integrated evolution"; Definition 2.1, p. 20). A force word is given by plain data: `nL` left marks at positions
`xL : Fin nL → ℝ` with weights `ρL : Fin nL → ℝ`, and `nR` right marks at positions `xR : Fin nR → ℝ` with weights
`ρR : Fin nR → ℝ` (the Lean index `i : Fin n` is the source index `i + 1`; the side label is the list a mark belongs
to, so a left mark at `0` is `0⁻` and a right mark at `0` is `0⁺`; coincident marks are kept as separate entries).
It is ordered when `x_{nL,L} ≤ ⋯ ≤ x_{1,L}`, `x_{1,L} ≤ 0`, `x_{1,R} ≤ ⋯ ≤ x_{nR,R}` and `0 ≤ x_{1,R}`; the weights
are arbitrary reals. -/
def IsOrderedForceWord {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Prop :=
  Antitone xL ∧ (∀ i, xL i ≤ 0) ∧ Monotone xR ∧ ∀ i, 0 ≤ xR i

end InteractingSLE
