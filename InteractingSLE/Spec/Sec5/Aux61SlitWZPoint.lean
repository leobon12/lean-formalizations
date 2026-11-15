/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWZRead
import InteractingSLE.Spec.Sec5.Aux61GR1FComponents

/-! # Basic restart clauses for the exact `RestartChoices.fam` chart

The existing chart-geometry field implies initial closure, the full
forward limit and pre-contact inclusion for this precise chosen chart.
It is not identified with the separately normalized X chart choice.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWZ
open Aux61SlitW Aux61SlitWX Aux61R1C Aux61Restart Aux61Asm2 Aux61FibData Aux61ULoc LawUnique

/-- The complete basic restart clauses from physical chart geometry.
The deterministic forward-tip theorem is supplied by the landed proof. -/
theorem restartPoint_of_geometry {W : ℝ → ℝ} {η : ℝ → ℂ} {K : Set ℂ} {r : ℝ≥0}
    {c : Chart} {b : ℂ} {ρ : ℝ≥0 → ℂ} {T : ℝ≥0∞}
    (hg : SourceChartGeometry W η K r c) (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : IsLoewnerTrace W η) (harc : WangWu.IsProperArc η) (hc : c.IsConformal)
    (hKo : IsOpen (H \ K)) (hclear : 0 < infDist (η r) K)
    (hdom : (c.dom : Set ℂ) = restartComponent K η r b)
    (hρ : Continuous ρ) (hversion : ∀ v : ℝ≥0, ρ v = η (r + (v : ℝ)))
    (hfirst : T = hitTime (fun _ : Unit => ρ) (fun _ => (H \ K)ᶜ) ()) : RestartPoint c ρ T := by
  have hzero : ρ 0 = η r := by simpa only [NNReal.coe_zero, add_zero] using hversion 0
  have hsub : (c.dom : Set ℂ) ⊆ H \ fwdHull W r := by
    rw [WangWu.fwdHull_eq_image_Ioc hη harc r.coe_nonneg]
    exact fun z hz => ⟨(hg.retained hz).1, fun hP =>
      (hg.retained hz).2 (Or.inr (image_mono Ioc_subset_Icc_self hP))⟩
  refine ⟨hρ, hc, ?_, ?_, fun v hv hvt =>
    continuation_mem_component hg hW hW0 hη harc hKo hclear hdom hρ hversion hfirst hv hvt⟩
  · rw [hzero]
    have : (𝓝[H] (0 : ℂ)).NeBot := PrimeEnd.approachH_neBot (0 : ℝ)
    exact mem_closure_of_tendsto (hη.tendsto_fwdMapInv_tip hW hW0 r.coe_nonneg)
      (eventually_mem_of_collar hg.collar)
  · rw [hzero]
    have hforward := (Aux61SlitWY.simpleTipForwardLimit hW hW0 hη harc r hg.start_pos).mono_left
      (nhdsWithin_mono _ hsub)
    refine (hg.current.comp hforward).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact congrArg c.1 (QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 r.coe_nonneg (hsub hz))

universe u
variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- Basic restart data for the literal family appearing in `ChoiceInputs`.
Its chart-geometry field is the only geometric input; no separate forward
tip, continuation, first-hit or restart-specification premise is needed. -/
theorem ae_restartPoint_of_chart_geometry (hsel : ∀ i, MeasurableSet (C.selected i))
    (hg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
        (GlueCond.cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) :
    ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
      RestartPoint (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
        (recordPath S (rationalTime (C.toR1Restart.q i)) p) (C.fam.contact i p) := by
  have R := readers C hsel
  have hrd := Aux61GR1F.recordDomainComponent_of_prefix_readers C.toR1Restart C.hasChart
    C.record_Y C.record_η C.q_nonneg
  have hdomain := dom_component_of_record S C.fam hrd (fun _ => Eventually.of_forall fun _ => rfl)
  intro i
  filter_upwards [hg i, hdomain i, R.ae_clearance i, S.physical_path, S.counterflow_retained_geometry,
    ae_recordPath S, r1_contact_fields_of_tipOff C.toR1Restart C.hasChart R.tipOff i]
    with p hgp hd hcl hp hcf hrp hct he
  obtain ⟨b, hb⟩ := hd he
  have hT : C.fam.contact i p = hitTime (fun _ : Unit => recordPath S (rationalTime (C.toR1Restart.q i)) p)
      (fun _ => (H \ GlueCond.cfHullQ (rationalTime S.s) p.2)ᶜ) () := by
    simpa only [RestartChoices.fam, Aux61Asm2.R1Restart.src, hitTime] using (hct he).1
  apply restartPoint_of_geometry (hgp he) hp.1.continuous_rpath
    (by simpa only [Ito.rpath, Real.toNNReal_zero] using hp.1.2.1) hp.2.1 hp.2.2
    ((C.toR1Restart.chart_spec C.hasChart i).2.1 _) (hcf (rationalTime S.s)).2.1 _ hb
    (hrp _).2.1 (fun v => ?_) hT
  · simpa only [Real.toNNReal_coe] using hcl he
  · simpa only [← NNReal.coe_add, Real.toNNReal_coe] using (hrp (rationalTime (C.toR1Restart.q i))).1 v

end InteractingSLE.Sec5.Aux61SlitWZ
