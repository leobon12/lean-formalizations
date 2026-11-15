/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWAAEndpoint

/-! # The original window excursion forces finite physical contact

A real counterflow-chart endpoint cannot be an interior physical point.
This discharges the finite-contact clause of `completed_window` for
selected records restarting at the original time, independently of the
retained restart chart's normalization or chosen capturing window.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAA
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61Asm2 Aux61FibData Aux61ULoc LawUnique
open WangWu

/-- A real limit in the counterflow chart at a finite excursion endpoint
places the continuous physical endpoint outside its interior domain. -/
theorem windowExcursion_endpoint_notMem {w : ℝ → ℝ} {η : ℝ → ℂ} {s t e : ℝ}
    {c : Aux61Kernel.WinCode} (hw : Continuous w) (hs : 0 ≤ s)
    (hη : ContinuousAt η e) (he : Aux61Kernel.WindowExcursion w s η t c e) :
    η e ∉ H \ Prop51G.cfHullQ w s := by
  obtain ⟨-, -, hte, hin, y, hy⟩ := he
  intro hmem
  have hηlim : Tendsto η (𝓝[<] e) (𝓝[H \ Prop51G.cfHullQ w s] (η e)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hη.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hte] with u hu using (hin u hu).1
  have hlim := ((continuousOn_revChart hw hs) (η e) hmem).tendsto.comp hηlim
  have heq : revChart w s (η e) = (y : ℂ) := tendsto_nhds_unique hlim hy
  have hH := revChart_mem_H hw hs hmem
  rw [heq] at hH
  exact (lt_irrefl (0 : ℝ)) (by simpa only [QuantumZipper.H, mem_ofPred_eq, Complex.ofReal_im] using hH)

universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The finite-contact part of the exact `completed_window` field holds
on the actual window event at every selected original-time index.
No chart-geometry, finite-buffer or completion premise is required. -/
theorem ae_contact_finite_at_original_time (hsel : ∀ i, MeasurableSet (C.selected i))
    (i : C.Idx) (hqi : C.q i.1 = S.t) :
    ∀ᵐ p ∂S.μ,
      sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
        C.toR1Restart.selected i → S.windowEvent p → C.fam.contact i p < ⊤ := by
  have R := Aux61SlitWZ.readers C hsel
  filter_upwards [S.physical_path, S.counterflow_good, ae_recordPath S,
    r1_contact_fields_of_tipOff C.toR1Restart C.hasChart R.tipOff i]
    with p hp hcf hrp hct he hwin
  have hq : C.toR1Restart.q i = S.t := hqi
  have hqcoe : (rationalTime (C.toR1Restart.q i) : ℝ) = (S.t : ℝ) := by
    rw [hq]
    exact Real.coe_toNNReal _ (by exact_mod_cast S.t_pos.le)
  obtain ⟨-, e, hex, -⟩ := hwin
  have hepos : 0 < e := (by exact_mod_cast S.t_pos : (0 : ℝ) < S.t).trans hex.2.2.1
  have hηc : ContinuousAt (fun t : ℝ => S.path p.1 t.toNNReal) e :=
    hp.2.2.cont.continuousAt (Ici_mem_nhds hepos)
  have hend := windowExcursion_endpoint_notMem (CfRegQ.reg_of_mem_goodCfSet hcf.1).2.1
    (by exact_mod_cast S.s_pos.le) hηc hex
  have hscoe : (rationalTime S.s : ℝ) = (S.s : ℝ) :=
    Real.coe_toNNReal _ (by exact_mod_cast S.s_pos.le)
  have hK : GlueCond.cfHullQ (rationalTime S.s) p.2 = Prop51G.cfHullQ (Prop411Q.cfDrv p.2) S.s := by
    rw [GlueCond.cfHullQ_eq_of_mem_goodCfSet hcf.1]
    exact congrArg (fun s => Prop51G.cfHullQ (Prop411Q.cfDrv p.2) s) hscoe
  let v : ℝ≥0 := ⟨e - (rationalTime (C.toR1Restart.q i) : ℝ), by
    rw [hqcoe]
    exact sub_nonneg.2 hex.2.2.1.le⟩
  have htime : rationalTime (C.toR1Restart.q i) + v = e.toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ hepos.le]
    exact add_sub_cancel _ _
  have hhit : recordPath S (rationalTime (C.toR1Restart.q i)) p v ∈
      (H \ GlueCond.cfHullQ (rationalTime S.s) p.2)ᶜ := by
    rw [(hrp _).1, htime, hK]
    exact hend
  have hle : C.fam.contact i p ≤ (v : ℝ≥0∞) := by
    change C.toR1Restart.contact i p ≤ _
    rw [(hct he).1]
    exact iInf₂_le v hhit
  exact hle.trans_lt ENNReal.coe_lt_top

end InteractingSLE.Sec5.Aux61SlitWAA
