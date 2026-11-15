/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow17Stop

/-! # Restart geometry for all selected refined windows

The canonical physical normalization and installed uniform seed collars
supply the selected-access landing clause in the exact restart geometry.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61GWindow17
open Aux61SlitW Aux61R1C Aux61Asm2 Aux61Restart Aux61FibData Aux61GInst Aux61GWord LawUnique
open WangWu (negInv)
universe u

/-- The full geometric clause is proved for the uniformly selected
canonical family. No chart geometry, seed window or landing hypothesis remains. -/
theorem refinedFamily_geometric (S : SourceSetting.{u}) : ∀ i, ∀ᵐ p ∂S.μ,
    p ∈ (refinedFamily S).event i → RestartGeoRest S (withRecordPath S (refinedFamily S)) i p := by
  let C := refinedChoices S
  have R := Aux61SlitWZ.readers C (refinedChoices_selected_measurable S)
  intro i
  filter_upwards [canonicalFamily_restartPoint C i, canonicalFamily_geometry C i,
    canonicalFamily_ae_domain C i, S.physical_path, S.counterflow_good,
    refinedFamily_seed S i, r1_contact_fields_of_tipOff C.toR1Restart C.hasChart R.tipOff i]
    with p hB hg hd hp hcf hseed hct he
  have B := hB he
  refine ⟨B.start_mem, B.start_lim, B.inside, ?_, (hg he).harmonic_lift⟩
  intro _ heq hfin
  obtain ⟨b, hbdom⟩ := hd he
  have hK := GlueCond.cfHullQ_eq_of_mem_goodCfSet hcf.1 (rationalTime S.s)
  rw [hK] at hbdom
  have hb : b ∈ retainedDomain (negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) ((refinedFamily S).start i) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ b).Nonempty
    rw [← hbdom]
    exact ⟨_, B.conformal.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hT : (refinedFamily S).contact i p = hitTime
      (fun _ : Unit => recordPath S ((refinedFamily S).start i) p)
      (fun _ => (H \ negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))ᶜ) () := by
    change C.toR1Restart.contact i p = hitTime
      (fun _ : Unit => recordPath S (rationalTime (C.toR1Restart.q i)) p)
      (fun _ => (H \ negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))ᶜ) ()
    simpa only [hitTime, hK] using (hct he).1
  let j := i.1.2.2.1.1
  have hbounded : Bornology.IsBounded (outerBuffer j) :=
    j.2.2.2.2.isBounded.subset subset_closure
  have hwindow : ((refinedFamily S).data i).V ⊆
      seedExitWindow (outerBuffer j) ((j : WindowIndex).2.2 : ℝ) := by
    intro z hz
    exact ⟨(windowGeometry j).window_sub hz, hz.2⟩
  apply Aux61SlitWX.landing_of_restartPoint he B (rationalTime S.s).coe_nonneg
    (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.2.2 (hp.2.2.cont.mono Icc_subset_Ici_self) _
    hb hbdom hT hbounded hwindow (hseed he) (hct he).2.1 heq hfin
  intro t ht
  rcases ht.1.eq_or_lt with ht0 | ht0
  · rw [← ht0]
    change S.path p.1 (0 : ℝ).toNNReal ∈ Hbar
    rw [hp.2.2.zero]
    exact zero_mem_Hbar
  · exact QuantumZipper.H_subset_Hbar (hp.2.2.mem_H t ht0)

end InteractingSLE.Sec5.Aux61GWindow17
