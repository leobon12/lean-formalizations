/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWZPoint
import InteractingSLE.Spec.Sec5.Aux61GR1FStop

/-! # The exact physical-stop and geometric fields of `ChoiceInputs`

The existing chart-geometry field and retained seed-window data supply
`geometric`. The physical inverse-window bound then supplies
`physical_stop`. These conclusions use the literal `C.fam` chart choice.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWZ
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61Asm2 Aux61FibData Aux61GInst Aux61ULoc LawUnique
open WangWu (negInv histLine)
universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The retained uniform seed-window choices for the exact `C.fam` chart.
The deterministic open/reference window fields are supplied separately. -/
structure SeedWindows where
  buffer : C.Idx → Set ℂ
  gap : C.Idx → ℝ
  bounded : ∀ i, Bornology.IsBounded (buffer i)
  window_subset : ∀ i, (C.toR1Restart.data i).V ⊆ seedExitWindow (buffer i) (gap i)
  seed : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → ∀ a : ℝ, |a| < gap i →
    boundedInverse (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) (a : ℂ) ∉
      oldModelBoundary (counterflowRecord (histLine p.2) (rationalTime S.s))

variable (hsel : ∀ i, MeasurableSet (C.selected i))
    (hg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (GlueCond.cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
include hsel hg

/-- The exact `ChoiceInputs.physical_stop` field. Event membership,
positive contact, own-path properness and pre-contact inclusion are proved;
only the physical inverse-window bound remains in addition to chart geometry. -/
theorem physical_stop_of_chart_geometry
    (hbounded : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.toR1Restart.event i → Bornology.IsBounded
      ((sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.1 ''
        ((C.toR1Restart.data i).V ∩ H))) :
    ∀ i, ∀ᵐ p ∂S.μ, sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      C.toR1Restart.selected i → p ∈ C.fam.event i ∧ 0 < C.fam.contact i p ∧
      (C.fam.contact i p < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < C.fam.contact i p ∧
        inPath (C.fam.event i)
          (sourceChart (withRecordPath S C.fam) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
          ((withRecordPath S C.fam).path i) (C.fam.contact i) p v ∉ (C.toR1Restart.data i).V) := by
  apply Aux61GR1F.physical_stop_of_bounded_inverse C.toR1Restart C.hasChart C.start_off ?_ hbounded
  intro i
  filter_upwards [ae_restartPoint_of_chart_geometry C hsel hg i] with p hp he
  exact (hp he).inside

/-- The exact `ChoiceInputs.geometric` field. All basic restart and landing
clauses follow from its existing chart-geometry field and retained seed windows. -/
theorem geometric_of_chart_geometry (V : SeedWindows C) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → RestartGeoRest S (withRecordPath S C.fam) i p := by
  have R := readers C hsel
  have hrd := Aux61GR1F.recordDomainComponent_of_prefix_readers C.toR1Restart C.hasChart
    C.record_Y C.record_η C.q_nonneg
  have hdomain := dom_component_of_record S C.fam hrd (fun _ => Eventually.of_forall fun _ => rfl)
  intro i
  filter_upwards [ae_restartPoint_of_chart_geometry C hsel hg i, hg i, hdomain i, S.physical_path,
    S.counterflow_good, V.seed i, r1_contact_fields_of_tipOff C.toR1Restart C.hasChart R.tipOff i]
    with p hB hgp hd hp hcf hgap hct he
  have B := hB he
  refine ⟨B.start_mem, B.start_lim, B.inside, ?_, (hgp he).harmonic_lift⟩
  intro _ heq hfin
  obtain ⟨b, hbdom⟩ := hd he
  have hK := GlueCond.cfHullQ_eq_of_mem_goodCfSet hcf.1 (rationalTime S.s)
  rw [hK] at hbdom
  change ((sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
    restartComponent (negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (C.toR1Restart.q i)) b at hbdom
  have hb : b ∈ retainedDomain (negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))
      (fun t : ℝ => S.path p.1 t.toNNReal) (rationalTime (C.toR1Restart.q i)) := by
    apply connectedComponentIn_nonempty_iff.1
    change (restartComponent _ _ _ b).Nonempty
    rw [← hbdom]
    exact ⟨_, B.conformal.inv_mem_dom (by change 0 < Complex.I.im; norm_num)⟩
  have hT : C.fam.contact i p = hitTime (recordPath S (rationalTime (C.toR1Restart.q i)))
      (fun _ => (H \ negInv '' fwdHull (Prop411Q.cfDrv p.2) (rationalTime S.s))ᶜ) p := by
    simpa only [RestartChoices.fam, Aux61Asm2.R1Restart.src, hitTime, hK] using (hct he).1
  apply landing_of_restartPoint he B (rationalTime S.s).coe_nonneg
    (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.2.2 (hp.2.2.cont.mono Icc_subset_Ici_self) _ hb hbdom hT
    (V.bounded i) (V.window_subset i) (hgap he) (hct he).2.1 heq hfin
  intro t ht
  rcases ht.1.eq_or_lt with ht0 | ht0
  · rw [← ht0]
    change S.path p.1 (0 : ℝ).toNNReal ∈ QuantumZipper.Hbar
    rw [hp.2.2.zero]
    exact zero_mem_Hbar
  · exact QuantumZipper.H_subset_Hbar (hp.2.2.mem_H t ht0)

end InteractingSLE.Sec5.Aux61SlitWZ
