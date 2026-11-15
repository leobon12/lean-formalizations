/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC7Seeds

/-!
# Initial heights depend only on the common offset

PROVE-SIDE-COLLAR2. The empty initial seed interval removes all dependence
on the supplied phase. Any two side data with the same offset therefore
have exactly the same initial-height requirement.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current

/-- Initial heights are invariant under every change of side data that
preserves the common offset, including arbitrary changes of phase. -/
theorem InitialReferenceHeightsExc.congr_offset
    {Ω : Type} [MeasurableSpace Ω] {i : BothLow} {d : WordObjects Ω}
    {side side' : SideTest Ω → Late.SideData Ω}
    {X : SideTest Ω → ℝ≥0 → Ω → Set ℂ}
    (h : InitialReferenceHeightsExc i d side X)
    (hOffset : ∀ j, (side j).offset = (side' j).offset) :
    InitialReferenceHeightsExc i d side' X := by
  intro j hj target e zL zR g₀ hg₀
  filter_upwards [h j hj g₀ hg₀] with ω hω hA ξ hξ hX
  have hlim := hω hA ξ hξ hX
  have hPhase := j.initial_phase_window_eq_zero hj hA ((side j).phase 0 ω) ξ
  have hPhase' := j.initial_phase_window_eq_zero hj hA ((side' j).phase 0 ω) ξ
  rw [hPhase, add_zero, hOffset j] at hlim
  rw [hPhase', add_zero]
  exact hlim

end InteractingSLE.Wire
