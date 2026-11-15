/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWAAEndpoint

/-! # A free seed collar for the literal selected choice family

This instantiates the physical retained-geometry theorem for `C.fam`
itself. The positive radius is pointwise; no initial-record localization
is asserted by this result.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAA
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61Asm2 Aux61FibData Aux61GInst Aux61ULoc LawUnique
open GlueCond WangWu
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- Every selected restart of the actual family has a positive real collar
avoiding the old counterflow boundary. Finite contact is unnecessary. -/
theorem ae_free_seed_gap (hsel : ∀ i, MeasurableSet (C.selected i))
    (hg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → ∃ δ > 0, ∀ a : ℝ, |a| < δ →
      boundedInverse (sourceChart C.fam
        (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) (a : ℂ) ∉
      oldModelBoundary (counterflowRecord (histLine p.2) (rationalTime S.s)) := by
  have R := Aux61SlitWZ.readers C hsel
  intro i
  filter_upwards [Aux61SlitWZ.ae_restartPoint_of_chart_geometry C hsel hg i, Aux61SlitWZ.ae_domain C i,
    S.physical_path, S.counterflow_good,
    r1_contact_fields_of_tipOff C.toR1Restart C.hasChart R.tipOff i]
    with p hB hd hp hcf hct he
  have B := hB he
  obtain ⟨b, hbdom⟩ := hd he
  have hK := cfHullQ_eq_of_mem_goodCfSet hcf.1 (rationalTime S.s)
  rw [hK] at hbdom
  have hb : b ∈ retainedDomain (negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (C.toR1Restart.q i)) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ b).Nonempty
    rw [← hbdom]
    exact ⟨_, B.conformal.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hT : (fun _ : Unit => C.fam.contact i p) = hitTime
      (fun _ => recordPath S (rationalTime (C.toR1Restart.q i)) p)
      (fun _ => (H \ negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))ᶜ) := by
    funext x
    simpa only [RestartChoices.fam, Aux61Asm2.R1Restart.src, hitTime, hK] using (hct he).1
  apply exists_glued_seed_gap B.unitSpec (rationalTime S.s).coe_nonneg
    (fun _ _ => (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.2.2)
    (fun _ _ => hp.2.2.cont.mono Icc_subset_Ici_self) (fun _ _ => ?_)
    (fun _ _ => hb) (fun _ _ => hbdom) hT () (mem_univ ()) (hct he).2.1
  intro t ht
  rcases ht.1.eq_or_lt with ht0 | ht0
  · rw [← ht0]
    change S.path p.1 (0 : ℝ).toNNReal ∈ Hbar
    rw [hp.2.2.zero]
    exact zero_mem_Hbar
  · exact QuantumZipper.H_subset_Hbar (hp.2.2.mem_H t ht0)

end InteractingSLE.Sec5.Aux61SlitWAA
