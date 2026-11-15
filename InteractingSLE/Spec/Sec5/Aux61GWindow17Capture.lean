/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Windows
import InteractingSLE.Spec.Sec5.Aux61GWindow17Access
import InteractingSLE.Spec.Sec5.Aux61SlitWAAContact
import InteractingSLE.Spec.Sec5.Aux61SlitWAACapture
import InteractingSLE.Spec.Sec5.Aux61SlitWAAUnit
import InteractingSLE.Spec.Sec5.Aux61GRecCapture

/-! # Match actual completions to the countable canonical family

Finite contact, normalization, inverse extension and a nonzero real
endpoint are proved from the source. The capturing index is selected
pointwise, while each family's chart, window and interval are fixed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData Aux61GInst Aux61GWord LawUnique
universe u

/-- Every physical source window event is captured by an actual index of
the constructed canonical family. This proves stay and fixed-interval
landing at that index, together with a finite physical inverse buffer.
It does not claim completion for every selected index. -/
theorem captureChoices_completed_cover (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → ∃ i,
      Aux61GRec.completedCapture (S.marksData (canonicalFamily (captureChoices S))) i p ∧
      ∀ z ∈ closure ((canonicalFamily (captureChoices S)).data i).buffer ∩ Hbar,
        boundedInverse (sourceChart (canonicalFamily (captureChoices S))
          (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) z ≠ 1 := by
  by_cases hgood : (goodSet (nL := S.nL) (nR := S.nR) (rationalTime S.s) S.t).Nonempty
  · let t : GoodTime S := ⟨S.t, hgood⟩
    let B := baseChoices S S.t
    let b : B.Idx := baseIndex S t
    have R := Aux61SlitWZ.readers B (fun _ => MeasurableSet.univ)
    filter_upwards [Aux61SlitWZ.ae_window_good_record S,
      Aux61SlitWAA.ae_contact_finite_at_original_time B (fun _ => MeasurableSet.univ) b rfl,
      canonicalFamily_restartPoint B b, canonicalFamily_inverse_continuous B b,
      canonicalFamily_real_endpoint B b,
      r1_contact_fields_of_tipOff B.toR1Restart B.hasChart R.tipOff b]
      with p hreg hfin hrestart hcont hend hcontact hwin
    have hb : p ∈ (canonicalFamily B).event b := ⟨mem_univ _, hreg hwin⟩
    have hf := hfin hb hwin
    have hp := (hcontact hb).2.1
    obtain ⟨y, hy, hl⟩ := hend hb hf
    have hlunit := hl
    rw [← Aux61SlitWAA.inPath_unit_eq hb] at hlunit
    obtain ⟨j, -, -, -, -, -, hfinite, -, -, hstay, -, -⟩ :=
      Aux61SlitWAA.exists_countable_finite_capture (hrestart hb).unitSpec (mem_univ ())
        hp hf (hcont hb) hy (by norm_num : (0 : ℝ) < 1) hlunit
        isOpen_univ (mem_univ _) (mem_univ _)
    obtain ⟨I, hI⟩ := exists_referenceInterval hy
    let C := captureChoices S
    let i : C.Idx := ⟨(I, j), hgood⟩
    have hi : p ∈ (canonicalFamily C).event i := ⟨mem_univ _, hreg hwin⟩
    have heq : inPath ((canonicalFamily B).event b)
        (sourceChart (canonicalFamily B) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life b)
        ((canonicalFamily B).path b) ((canonicalFamily B).contact b) p =
      inPath ((canonicalFamily C).event i)
        (sourceChart (canonicalFamily C) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((canonicalFamily C).path i) ((canonicalFamily C).contact i) p := rfl
    refine ⟨i, ⟨hi, hf, ?_, y, ?_, ?_⟩, ?_⟩
    · intro v hv
      have hs := hstay v hv
      rw [Aux61SlitWAA.inPath_unit_eq hb] at hs
      change inPath ((canonicalFamily B).event b)
        (sourceChart (canonicalFamily B) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life b)
        ((canonicalFamily B).path b) ((canonicalFamily B).contact b) p v ∈ bufferedWindow j at hs
      rw [heq] at hs
      exact hs
    · change y ∈ Ioo (intervalWord S I).left (intervalWord S I).right
      rw [intervalWord_left, intervalWord_right]
      exact hI
    · exact heq ▸ hl
    · exact hfinite
  · filter_upwards [Aux61SlitWZ.ae_window_good_record S] with p hp hw
    exact (hgood ⟨actRec S S.t p, hp hw⟩).elim

end InteractingSLE.Sec5.Aux61GWindow17
