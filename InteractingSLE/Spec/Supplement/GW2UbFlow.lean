/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UbSep

/-!
# The far right mark of a flow line is swallowed on an infinite lifetime (the piece for STAGEMEAN, D76 (2))

Packet PROVE-GW2-RELDET (round 38, decision D73 route (ii); the second split of D76). `ae_exists_swallow_of_top`
(`GW2UbSep.lean`) proves, for an integrated `SLE_κ(ρ)` evolution of a distinct word, that a right mark `x_j` (`j ≥ 1`)
is swallowed on an infinite lifetime when the total right weight is `< κ/2 − 2` (the target change of LP9, then Lemma
G12 at the old target's image `−1`). The tip exclusion of the stopped stage law needs it for the flow line of a GFF
with the data of a sorted word (the stage field in the relative chart, `StageFieldLawXStatement`), with the mark read
from the driver alone:

* **`FlowSwallowStatement`**: for a flow-line driver at angle `0` of a GFF with piecewise-constant data `b` whose right
  total weight is `< κ/2 − 2`, almost surely, on an infinite lifetime, the driver meets the Loewner image of every
  point `y > 0` (the point `y` is swallowed; it need not be a jump of `b`).

PROVE-GW2-STAGEMEAN proves it (D76 (2)) from `ae_exists_swallow_of_top`: the flow-line word is distinct; if `y` is not
a jump, add it as a passive right mark (weight `0`; `Sec2.IsSLEEvolutionUpTo.exists_addMarks` / `of_passive`), which
leaves the total right weight unchanged; `y` is then a right mark of Lean index `≥ 1`, after a reindexing of the right
list as `j + 1 + m`; the force point of `y` is its Loewner image `rightImg` before it is swallowed. RELDET consumes it
as stated (at the far junction of the stage word, which need not be a jump).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

/-- **The far right mark of a flow line is swallowed on an infinite lifetime** (for PROVE-GW2-STAGEMEAN, D76 (2)). For
`0 < κ < 4`, a flow-line driver at angle `0` (`IsFlowLineDriver`, seed `0`) of a GFF with data `b` whose total right
weight `Σ flowLineRhoR` is `< κ/2 − 2`, and a point `y > 0` (a jump of `b` or not): almost surely, if the lifetime is
infinite, the Loewner image of `y` meets the driver at some time. -/
def FlowSwallowStatement : Prop :=
  ∀ {κ : ℝ}, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ) (y : ℝ), 0 < y →
    ∑ i, flowLineRhoR κ b jumps 0 0 i < κ / 2 - 2 →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsFlowLineDriver κ b jumps 0 P h W ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ → ∃ t : ℝ≥0, MartChar.RealFlow.rightImg (fun s : ℝ => W s.toNNReal ω) y t ≤ W t ω

end InteractingSLE.Theorem14.GW2Rd
