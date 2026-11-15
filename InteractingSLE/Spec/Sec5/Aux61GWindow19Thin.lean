/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow19Windows
import InteractingSLE.Spec.Sec5.Aux61SlitWACAccess

/-! # Actual captures in any prescribed seed and landing neighborhood

The real neighborhood may be chosen after the actual endpoint is known.
It may be a disjoint seed part and landing part. The selected buffer is
finite and its seed gap belongs to the record's fixed Borel seed piece.
No reference height, branch or access-selection hypothesis is used here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow19
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61GR1F Aux61GWord Aux61GInst Aux61FibData LawUnique
universe u

/-- The fixed normalized source used to read an actual continuation. -/
abbrev timeSource (S : SourceSetting.{u}) (t : Aux61GWindow17.GoodTime S) :=
  Aux61GWindow17.canonicalFamily (Aux61GWindow17.baseChoices S t.1)

abbrev timeIndex (S : SourceSetting.{u}) (t : Aux61GWindow17.GoodTime S) : (timeSource S t).ι :=
  Aux61GWindow17.baseIndex S t

abbrev timeRecord (S : SourceSetting.{u}) (t : Aux61GWindow17.GoodTime S) :=
  sourceRecord (timeSource S t) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (timeIndex S t)

abbrev timeContact (S : SourceSetting.{u}) (t : Aux61GWindow17.GoodTime S) :=
  (timeSource S t).contact (timeIndex S t)

abbrev timePath (S : SourceSetting.{u}) (t : Aux61GWindow17.GoodTime S) :=
  inPath ((timeSource S t).event (timeIndex S t))
    (sourceChart (timeSource S t) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (timeIndex S t))
    ((timeSource S t).path (timeIndex S t)) (timeContact S t)

/-- Every source window event has a nonzero actual endpoint and a fixed
seed piece admitting captures in every open real neighborhood of zero and
that endpoint. This includes R103's thin seed-plus-landing neighborhoods. -/
theorem ae_capture_in_real_open (S : SourceSetting.{u}) : ∀ᵐ p ∂S.μ,
    S.windowEvent p → ∃ t : Aux61GWindow17.GoodTime S, t.1 = S.t ∧ ∃ k : ℕ × ℕ,
      timeRecord S t p ∈ Aux61GWindow17.seedPiece S t k ∧
      0 < timeContact S t p ∧ timeContact S t p < ⊤ ∧ ∃ y : ℝ, y ≠ 0 ∧
      Tendsto (timePath S t p) (𝓝[<] (timeContact S t p).toNNReal) (𝓝 (y : ℂ)) ∧
      ∀ O : Set ℝ, IsOpen O → 0 ∈ O → y ∈ O →
        ∃ J : Aux61GWindow17.AllowedWindow, J.1.2 = k ∧
          timeRecord S t p ∈ Aux61GWindow17.windowRecords S t J ∧
          (∀ z ∈ closure (outerBuffer J.1.1), z.im = 0 → z.re ∈ O) ∧
          (∀ v : ℝ≥0, (v : ℝ≥0∞) < timeContact S t p → timePath S t p v ∈ bufferedWindow J.1.1) ∧
          (y : ℂ) ∉ bufferedWindow J.1.1 := by
  by_cases hgood : (goodSet (nL := S.nL) (nR := S.nR) (rationalTime S.s) S.t).Nonempty
  · let t : Aux61GWindow17.GoodTime S := ⟨S.t, hgood⟩
    let B := Aux61GWindow17.baseChoices S S.t
    let b : B.Idx := Aux61GWindow17.baseIndex S t
    have R := Aux61SlitWZ.readers B (fun _ => MeasurableSet.univ)
    filter_upwards [Aux61SlitWZ.ae_window_good_record S, Aux61GWindow17.ae_record_mem_seedRecords S t,
      Aux61SlitWAA.ae_contact_finite_at_original_time B (fun _ => MeasurableSet.univ) b rfl,
      Aux61GWindow17.canonicalFamily_restartPoint B b,
      Aux61GWindow17.canonicalFamily_inverse_continuous B b,
      Aux61GWindow17.canonicalFamily_real_endpoint B b,
      r1_contact_fields_of_tipOff B.toR1Restart B.hasChart R.tipOff b]
      with p hreg hseed hfin hrestart hcont hend hcontact hw
    have hb : p ∈ (timeSource S t).event (timeIndex S t) := ⟨mem_univ _, hreg hw⟩
    have hs := hseed hb
    have hcert : timeRecord S t p ∈ Aux61GWindow17.certifiedRecords S t := by
      obtain ⟨y, -, hy⟩ := hs
      change sourceRecord (Aux61GWindow17.canonicalFamily B) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life b p ∈ Aux61GWindow17.certifiedRecords S t
      exact hy ▸ y.2
    rw [Aux61GWindow17.seedPieces_cover, mem_iUnion] at hs
    obtain ⟨k, hk⟩ := hs
    have hf := hfin hb hw
    obtain ⟨y, hy, hl⟩ := hend hb hf
    refine ⟨t, rfl, k, hk, (hcontact hb).2.1, hf, y, hy, hl, ?_⟩
    intro O hO hO0 hOy
    have hlunit := hl
    rw [← Aux61SlitWAA.inPath_unit_eq hb] at hlunit
    obtain ⟨j, -, hjgap, -, -, -, hfinite, -, hreal, hstay, hout, -⟩ :=
      Aux61SlitWAA.exists_countable_finite_capture (hrestart hb).unitSpec (mem_univ ())
        (hcontact hb).2.1 hf (hcont hb) hy (collarRadius_pos k.1) hlunit hO hO0 hOy
    let J : Aux61GWindow17.AllowedWindow := ⟨(j, k), hjgap.le⟩
    refine ⟨J, rfl, ⟨hcert, hfinite, hk⟩, hreal, ?_, hout⟩
    intro v hv
    have hs := hstay v hv
    rw [Aux61SlitWAA.inPath_unit_eq hb] at hs
    exact hs
  · filter_upwards [Aux61SlitWZ.ae_window_good_record S] with p hp hw
    exact (hgood ⟨Aux61R1C.actRec S S.t p, hp hw⟩).elim

end InteractingSLE.Sec5.Aux61GWindow19
