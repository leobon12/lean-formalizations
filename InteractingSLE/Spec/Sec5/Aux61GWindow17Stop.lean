/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Refine

/-! # Physical stopping for every selected refined window

The retained-record restrictions supply the physical inverse bound.
Properness of the actual continuation gives a window exit when contact
is infinite. No stopping or finite-buffer premise is supplied.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData Aux61GInst LawUnique
universe u

/-- The exact physical-stop clause for the actual refined canonical
source, for all selected records and their installed windows. -/
theorem refinedFamily_physical_stop (S : SourceSetting.{u}) : ∀ i, ∀ᵐ p ∂S.μ,
    sourceRecord (refinedFamily S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      (refinedFamily S).selected i →
    p ∈ (refinedFamily S).event i ∧ 0 < (refinedFamily S).contact i p ∧
      ((refinedFamily S).contact i p < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < (refinedFamily S).contact i p ∧
        inPath ((refinedFamily S).event i)
          (sourceChart (refinedFamily S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
          ((refinedFamily S).path i) ((refinedFamily S).contact i) p v ∉ ((refinedFamily S).data i).V) := by
  let C := refinedChoices S
  have R := Aux61SlitWZ.readers C (refinedChoices_selected_measurable S)
  intro i
  filter_upwards [canonicalFamily_restartPoint C i,
    r1_contact_fields_of_tipOff C.toR1Restart C.hasChart R.tipOff i,
    Aux61GR1F.ae_recordPath_proper S] with p hB hc hp hy
  have he : p ∈ (refinedFamily S).event i := hy
  refine ⟨he, (hc he).2.1, ?_⟩
  by_cases hf : (refinedFamily S).contact i p < ⊤
  · exact Or.inl hf
  · have htop : (refinedFamily S).contact i p = ⊤ := top_unique (not_lt.1 hf)
    exact Or.inr (Aux61GR1F.exists_exit_of_contact_top he (hB he).conformal htop
      (fun v hv => (hB he).inside v hv (htop ▸ ENNReal.coe_lt_top)) (hp _)
      (refinedFamily_inverse_bounded S i p he))

end InteractingSLE.Sec5.Aux61GWindow17
