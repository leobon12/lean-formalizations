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

/-- The force-word boundary data of Theorem 1.1 (p. 9) for the weights `(ρL; ρR)` at a state whose centred
force-point positions are `vL i = V̂^{i+1,L}`, `vR i = V̂^{i+1,R}`: with `λ = π/√κ`,
`−λ (1 + ∑_{i=0}^{j} ρ^{i,L})` on `[V̂^{j+1,L}, V̂^{j,L})` and `λ (1 + ∑_{i=0}^{j} ρ^{i,R})` on
`[V̂^{j,R}, V̂^{j+1,R})` (`V̂^{0,q} = 0`, `V̂^{k+1,L} = −∞`, `V̂^{ℓ+1,R} = ∞`, `ρ^{0,q} = 0`).
For `x < 0` the left marks strictly to the right of `x` are exactly the marks `1, …, j` of the
interval containing `x`; for `x ≥ 0` the right marks at or to the left of `x` are the marks
`1, …, j`. Intervals of zero length contribute no point. -/
def forceBoundaryData (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) (x : ℝ) : ℝ :=
  if x < 0 then
    -(Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ Finset.univ.filter (fun i => x < vL i), ρL i)
  else
    (Real.pi / Real.sqrt κ) * (1 + ∑ i ∈ Finset.univ.filter (fun i => vR i ≤ x), ρR i)

end InteractingSLE
