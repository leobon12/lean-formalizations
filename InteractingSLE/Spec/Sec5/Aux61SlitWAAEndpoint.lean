/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWAAUnit
import InteractingSLE.Spec.Sec5.Aux61SlitWZInverse
import InteractingSLE.Spec.Sec5.Aux61SlitWZTopology

/-! # A nonzero real selected endpoint for the literal choice family

The existing `chart_geometry` field supplies the required normalization.
All physical first-contact and selected-access clauses are proved for the
actual `C.fam`, without identifying it with another chart choice.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAA
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61Asm2 Aux61FibData Aux61ULoc LawUnique
open GlueCond WangWu
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- Finite contact in the exact chosen family has a nonzero real selected
endpoint, from the existing geometry field and no extra access hypothesis. -/
theorem ae_real_endpoint (hsel : ∀ i, MeasurableSet (C.selected i))
    (hg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → C.fam.contact i p < ⊤ → ∃ y : ℝ, y ≠ 0 ∧
      Tendsto (inPath (C.fam.event i)
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (recordPath S (rationalTime (C.toR1Restart.q i))) (C.fam.contact i) p)
        (𝓝[<] (C.fam.contact i p).toNNReal) (𝓝 (y : ℂ)) := by
  have R := Aux61SlitWZ.readers C hsel
  intro i
  filter_upwards [Aux61SlitWZ.ae_restartPoint_of_chart_geometry C hsel hg i, Aux61SlitWZ.ae_domain C i,
    hg i, S.physical_path, S.counterflow_good, ae_recordPath S,
    r1_contact_fields_of_tipOff C.toR1Restart C.hasChart R.tipOff i]
    with p hB hd hgp hp hcf hrp hct he hfin
  obtain ⟨b, hbdom⟩ := hd he
  have hK := cfHullQ_eq_of_mem_goodCfSet hcf.1 (rationalTime S.s)
  rw [hK] at hbdom
  have B := hB he
  have hb : b ∈ retainedDomain (negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (C.toR1Restart.q i)) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ b).Nonempty
    rw [← hbdom]
    exact ⟨_, B.conformal.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hT : C.fam.contact i p = hitTime (fun _ : Unit => recordPath S (rationalTime (C.toR1Restart.q i)) p)
      (fun _ => (H \ negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))ᶜ) () := by
    simpa only [RestartChoices.fam, Aux61Asm2.R1Restart.src, hitTime, hK] using (hct he).1
  have hgeom := hgp he
  rw [hK] at hgeom
  obtain ⟨y, hy, hlim⟩ := exists_real_source_accessEndpoint B.unitSpec (mem_univ ())
    (hct he).2.1 hfin hp.1.continuous_rpath
    (by simpa only [Ito.rpath, Real.toNNReal_zero] using hp.1.2.1) hp.2.1 hp.2.2
    (rationalTime S.s).coe_nonneg (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.2.2 hb hbdom hgeom hT
    (fun v _ _ => by
      simpa only [← NNReal.coe_add, Real.toNNReal_coe] using (hrp (rationalTime (C.toR1Restart.q i))).1 v)
  refine ⟨y, hy, ?_⟩
  have hpath := inPath_unit_eq
    (c := sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
    (ρ := recordPath S (rationalTime (C.toR1Restart.q i))) (T := C.fam.contact i) he
  rwa [hpath] at hlim

end InteractingSLE.Sec5.Aux61SlitWAA
