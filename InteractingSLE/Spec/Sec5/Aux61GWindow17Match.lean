/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Facts

/-! # Completed captures match the uniformly restricted source family

The actual continuation chooses a countable capturing index. Its initial
record satisfies that index's already fixed Borel tests, and its chart is
exactly the same canonical time chart. The regular cut loses no captures.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData Aux61GInst Aux61GWord LawUnique
universe u

/-- Every source window event has a capturing index satisfying its fixed
initial-record seed and buffer tests. No capture predicate is used in
the selection of the record event. -/
theorem refinedFamily_completed_cover (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → ∃ i, Aux61GRec.completedCapture (S.marksData (refinedFamily S)) i p := by
  by_cases hgood : (Aux61R1C.goodSet (nL := S.nL) (nR := S.nR) (rationalTime S.s) S.t).Nonempty
  · let t : GoodTime S := ⟨S.t, hgood⟩
    let B := baseChoices S S.t
    let b : B.Idx := baseIndex S t
    have R := Aux61SlitWZ.readers B (fun _ => MeasurableSet.univ)
    filter_upwards [Aux61SlitWZ.ae_window_good_record S, ae_record_mem_seedRecords S t,
      Aux61SlitWAA.ae_contact_finite_at_original_time B (fun _ => MeasurableSet.univ) b rfl,
      canonicalFamily_restartPoint B b, canonicalFamily_inverse_continuous B b,
      canonicalFamily_real_endpoint B b,
      r1_contact_fields_of_tipOff B.toR1Restart B.hasChart R.tipOff b]
      with p hreg hseed hfin hrestart hcont hend hcontact hwin
    have hb : p ∈ (canonicalFamily B).event b := ⟨mem_univ _, hreg hwin⟩
    have hs := hseed hb
    have hcert : sourceRecord (canonicalFamily B) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life b p ∈ certifiedRecords S t := by
      obtain ⟨y, -, hy⟩ := hs
      exact hy ▸ y.2
    rw [seedPieces_cover, mem_iUnion] at hs
    obtain ⟨k, hk⟩ := hs
    have hf := hfin hb hwin
    obtain ⟨y, hy, hl⟩ := hend hb hf
    have hlunit := hl
    rw [← Aux61SlitWAA.inPath_unit_eq hb] at hlunit
    obtain ⟨j, -, hjgap, -, -, -, hfinite, -, -, hstay, -, -⟩ :=
      Aux61SlitWAA.exists_countable_finite_capture (hrestart hb).unitSpec (mem_univ ())
        (hcontact hb).2.1 hf (hcont hb) hy (collarRadius_pos k.1) hlunit
        isOpen_univ (mem_univ _) (mem_univ _)
    obtain ⟨I, hI⟩ := exists_referenceInterval hy
    let J : AllowedWindow := ⟨(j, k), hjgap.le⟩
    let i : (refinedChoices S).Idx := ⟨(t, I, J), hgood⟩
    have hw : sourceRecord (refinedFamily S) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p ∈ windowRecords S t J := ⟨hcert, hfinite, hk⟩
    have hi : p ∈ (refinedFamily S).event i := ⟨hw, hreg hwin⟩
    have heq : inPath ((canonicalFamily B).event b)
        (sourceChart (canonicalFamily B) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life b)
        ((canonicalFamily B).path b) ((canonicalFamily B).contact b) p =
      inPath ((refinedFamily S).event i)
        (sourceChart (refinedFamily S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((refinedFamily S).path i) ((refinedFamily S).contact i) p := by
      funext v
      simp only [inPath, hb, hi, true_and]
      rfl
    refine ⟨i, hi, hf, ?_, y, ?_, heq ▸ hl⟩
    · intro v hv
      have hv' := hstay v hv
      rw [Aux61SlitWAA.inPath_unit_eq hb] at hv'
      change inPath ((canonicalFamily B).event b)
        (sourceChart (canonicalFamily B) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life b)
        ((canonicalFamily B).path b) ((canonicalFamily B).contact b) p v ∈ bufferedWindow j at hv'
      rw [heq] at hv'
      exact hv'
    · change y ∈ Ioo (intervalWord S I).left (intervalWord S I).right
      rw [intervalWord_left, intervalWord_right]
      exact hI
  · filter_upwards [Aux61SlitWZ.ae_window_good_record S] with p hp hw
    exact (hgood ⟨actRec S S.t p, hp hw⟩).elim

/-- The same captured cover on the full-measure cut whose pointwise
restart facts are `refinedFamily_cut_restart`. -/
theorem refinedFamily_completed_cover_cut (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → ∃ i, Aux61GRec.completedCapture
      (S.marksData (cutSource S (withRecordPath S (refinedFamily S)))) i p := by
  filter_upwards [refinedFamily_completed_cover S, refinedFamily_ae_good S] with p hc hg hw
  obtain ⟨i, hi, hf, hs, y, hy, hl⟩ := hc hw
  have he : p ∈ (refinedFamily S).event i := hi
  have hcut : p ∈ (cutSource S (withRecordPath S (refinedFamily S))).event i := ⟨he, hg⟩
  have heq : inPath ((cutSource S (withRecordPath S (refinedFamily S))).event i)
      (sourceChart (cutSource S (withRecordPath S (refinedFamily S)))
        (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((cutSource S (withRecordPath S (refinedFamily S))).path i)
      ((cutSource S (withRecordPath S (refinedFamily S))).contact i) p =
    inPath ((refinedFamily S).event i)
      (sourceChart (refinedFamily S) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((refinedFamily S).path i) ((refinedFamily S).contact i) p := by
    funext v
    simp only [inPath, hcut, he, true_and]
    rfl
  refine ⟨i, hi, hf, ?_, y, hy, ?_⟩
  · intro v hv
    change inPath ((cutSource S (withRecordPath S (refinedFamily S))).event i)
      (sourceChart (cutSource S (withRecordPath S (refinedFamily S)))
        (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((cutSource S (withRecordPath S (refinedFamily S))).path i)
      ((cutSource S (withRecordPath S (refinedFamily S))).contact i) p v ∈
      ((cutSource S (withRecordPath S (refinedFamily S))).data i).V
    rw [heq]
    exact hs v hv
  · change Tendsto (inPath ((cutSource S (withRecordPath S (refinedFamily S))).event i)
      (sourceChart (cutSource S (withRecordPath S (refinedFamily S)))
        (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      ((cutSource S (withRecordPath S (refinedFamily S))).path i)
      ((cutSource S (withRecordPath S (refinedFamily S))).contact i) p)
      (𝓝[<] ((cutSource S (withRecordPath S (refinedFamily S))).contact i p).toNNReal) (𝓝 (y : ℂ))
    rw [heq]
    exact hl

end InteractingSLE.Sec5.Aux61GWindow17
