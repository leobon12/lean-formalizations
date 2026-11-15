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

/-- The continuation-threshold condition at a state `(w, vL, vR)` of a force word with weights `(ρL; ρR)`
(Specification p. 3, display defining `T_*`; Definition 2.1, p. 20): for some side `q ∈ {L, R}`,
`∑_{i : v^{i,q} = w} ρ^{i,q} ≤ -2`. An empty sum is `0`, so it does not trigger. -/
def ForceWord.ThresholdCondition {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ)
    (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) : Prop :=
  (∑ i ∈ Finset.univ.filter (fun i => vL i = w), ρL i) ≤ -2 ∨
    (∑ i ∈ Finset.univ.filter (fun i => vR i = w), ρR i) ≤ -2

end InteractingSLE
