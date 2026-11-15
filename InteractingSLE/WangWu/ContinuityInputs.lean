/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsGeneratingTrace
import InteractingSLE.Frozen.Spec.IsOrderedForceWord

/-!
# Wang–Wu at `κ = 4`: External input 8.3 (Zhan's nonboundary transience), as a named hypothesis

Packet PROVE-WW-C. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §8, External input 8.3
(p. 51): "For `κ = 4`, suppose all force points are strictly separated from the start, and every cumulative
weight on each side is nonnegative. The chordal force-point trace has terminal limit `∞`. When its SDE lifetime
is infinite, this means `lim_{t→∞} γ(t) = ∞`. Source: Zhan [5, Theorem 4.2], specialized to `κ = 4`. The stated
source permits empty side lists."

The packet (PROVE-WW-C, "Coordination") fixes that this input, which is with an external mathematician, is
stated as a distinct named hypothesis exactly as the document's §8 does; it is **not** proved here and must
appear as an explicit hypothesis of every theorem that uses it (Proposition 6.6, case `α ≥ 0`; the
non-boundary-intersecting seed; Theorem 7.7, case "all `r_j ≥ 0`").

`ZhanNonboundaryTransience` reads the input with the frozen carriers: the force-point process is an integrated
evolution at `a = κ = 4` (`IsIntegratedSLEEvolution 4`, Definition 1.3 = input 8.1); the marks are strictly
separated from the start (`x_{i,L} < 0 < x_{j,R}`); every cumulative weight `∑_{i ≤ k} ρ_{i,q}`, counted from the
mark nearest the start, is nonnegative; and the conclusion is that almost surely every continuous generating
trace of the chain on an infinite lifetime tends to `∞`. (With nonnegative cumulative weights the continuation
threshold is never reached, so the lifetime is infinite; that consequence of input 8.1 is not part of the
input.) The trace itself is not asserted to exist ("Our application first constructs the trace").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

/-- **External input 8.3** (Zhan, *Duality of chordal SLE, II*, Theorem 4.2 at `κ = 4`; document §8): for force
data strictly separated from the start with every cumulative weight on each side nonnegative, the chordal
force-point trace tends to `∞` when the SDE lifetime is infinite. A named hypothesis (packet PROVE-WW-C); not
proved in the project. -/
def ZhanNonboundaryTransience.{u} : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → (∀ i, xL i < 0) → (∀ j, 0 < xR j) →
    (∀ k : Fin nL, 0 ≤ ∑ i ∈ univ.filter (fun i => i ≤ k), ρL i) →
    (∀ k : Fin nR, 0 ≤ ∑ j ∈ univ.filter (fun j => j ≤ k), ρR j) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution 4 xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
        Tendsto (fun t => ‖η t‖) atTop atTop

end WangWu

end InteractingSLE
