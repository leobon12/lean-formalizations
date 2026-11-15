/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.Aux7

/-!
# Wang–Wu's External input 8.3 (Zhan's nonboundary transience at `κ = 4`), from transience for separated words

Packet PROVE-ZHAN-B2. `WangWu.ZhanNonboundaryTransience` (PROVE-WW-C's named input; document §8, input 8.3: "For
`κ = 4`, suppose all force points are strictly separated from the start, and every cumulative weight on each side is
nonnegative. The chordal force-point trace has terminal limit `∞`") is the case `κ = 4` of the separated core
`Zhan.SeparatedTransienceStatement`: nonnegative cumulative weights are admissible side partial sums at `κ = 4`
(`WangWu.HasNonnegCumWeights.hasAdmissiblePartialSums`, `c = κ/2 − 2 = 0`).

## Main results

* `zhanNonboundaryTransience_of_separatedTransience`: `WangWu.ZhanNonboundaryTransience` from
  `SeparatedTransienceStatement 4`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Zhan

/-- **Wang–Wu's External input 8.3**, from the separated core at `κ = 4`. -/
theorem zhanNonboundaryTransience_of_separatedTransience (hS : SeparatedTransienceStatement.{u} 4) :
    WangWu.ZhanNonboundaryTransience.{u} := by
  intro nL nR xL xR ρL ρR hF hxL hxR hcL hcR Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hcum : WangWu.HasNonnegCumWeights ρL ρR :=
    ⟨fun k => by rw [← WangWu.filter_le_eq_Iic]; exact hcL k,
      fun k => by rw [← WangWu.filter_le_eq_Iic]; exact hcR k⟩
  have hadm := hcum.hasAdmissiblePartialSums hF
  filter_upwards [hS xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hxL hxR hE] with ω hω hζ η hη
  rw [hζ] at hη
  exact hω η hη

end InteractingSLE.Zhan
