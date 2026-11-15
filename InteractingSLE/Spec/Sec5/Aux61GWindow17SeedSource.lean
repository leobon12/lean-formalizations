/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Seed

/-! # Actual source records belong to the canonical seed pieces

The normalized inverse at zero is the physical restart point. Its positive
clearance from the retained counterflow boundary gives the required Borel
seed event without a normalization or seed-window hypothesis.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61FibData Aux61GInst Aux61ULoc LawUnique
universe u

/-- Every selected actual record at a regular time has positive seed
clearance for the canonical chart, almost surely. -/
theorem ae_record_mem_seedRecords (S : SourceSetting.{u}) (t : GoodTime S) :
    let B := baseChoices S t.1
    let i := baseIndex S t
    ∀ᵐ p ∂S.μ, p ∈ B.fam.event i →
      sourceRecord (canonicalFamily B) (rationalTime S.s)
        S.own.W S.own.VL S.own.VR S.life i p ∈ seedRecords S t := by
  dsimp only
  let B := baseChoices S t.1
  let i := baseIndex S t
  have R := Aux61SlitWZ.readers B (fun _ => MeasurableSet.univ)
  filter_upwards [Aux61SlitWAB.ae_record_mem_certifiedSelection B i,
    canonicalFamily_restartPoint B i, canonicalFamily_inverse_continuous B i,
    r1_contact_fields_of_tipOff B.toR1Restart B.hasChart R.tipOff i, S.counterflow_good]
    with p hcert hB hcont hct hcf he
  have hc := hcert he
  let y : certifiedRecords S t :=
    ⟨sourceRecord (canonicalFamily B) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p, hc⟩
  have hzero := boundedInverse_zero_of_restartSpec (hB he).unitSpec (mem_univ ())
    (hct he).2.1 (recordChart_extension S t hc).1 (hcont he)
  change boundedInverse (recordChart S t y.1) 0 = _ at hzero
  have hfill := fillH_clipped_trace (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.2.2
    (rationalTime S.s).coe_nonneg
  change fillH (counterflowRecord (WangWu.histLine p.2) (rationalTime S.s)) = _ at hfill
  have hstart : recordPath S (rationalTime t.1) p 0 ∈
      H \ WangWu.negInv '' fillH (counterflowRecord (WangWu.histLine p.2) (rationalTime S.s)) := by
    rw [hfill, ← GlueCond.cfHullQ_eq_of_mem_goodCfSet hcf.1 (rationalTime S.s)]
    exact (hct he).2.2
  have hnot := cayley_notMem_oldModelBoundary
    (K := counterflowRecord (WangWu.histLine p.2) (rationalTime S.s))
    (by rintro _ ⟨a, -, rfl⟩; exact clipH_mem_Hbar _) hstart
  have hn : boundedInverse (recordChart S t y.1) 0 ∉
      Aux61SlitWAB.recordBoundary (rationalTime S.s) y.1.1 := by
    change boundedInverse (recordChart S t y.1) 0 ∉
      Aux61SlitWAB.recordBoundary (rationalTime S.s) (stopRec (rationalTime S.s) p.2)
    rw [Aux61SlitWAB.recordBoundary_stopRec_eq hcf.1.1.2, hzero]
    exact hnot
  refine ⟨y, ?_, rfl⟩
  exact ((Aux61SlitWAB.isCompact_recordBoundary (rationalTime_s_pos S) hc.2).isClosed.notMem_iff_infDist_pos
    (Aux61SlitWAB.recordBoundary_nonempty _ _)).1 hn

end InteractingSLE.Sec5.Aux61GWindow17
