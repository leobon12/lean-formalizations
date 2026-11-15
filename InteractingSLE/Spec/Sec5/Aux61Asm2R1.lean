/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Asm2Path
import InteractingSLE.Spec.Sec5.Aux61MarksSetOn
import InteractingSLE.Spec.Sec5.Aux61MarksContact
import InteractingSLE.Spec.Sec5.Aux61GAlignCutoffs
import InteractingSLE.Spec.Sec5.CrossCondTheta

/-!
# The contact rule, R1's chart domain and the initial data wired into the assembled fibre cover

Packet PROVE-AUX61-ASSEMBLE2 (second round). Three inputs of `RecordInputs` are discharged from committed results:

* **the contact rule** — `Ta i := contactRule (C i) (start i)` (PROVE-AUX61-MARKS' first-hit rule of a closed obstacle
  read at the restart time): measurable, Galmarino, and almost surely on the event equal to `start + contact` once the
  contact is the first hitting time of the obstacle by the restart path, starting off it
  (`contact_rule_of_hit`, via MARKS' `contactRule_eq_add_hitTime`); R1's obstacle `retObs` qualifies;
* **R1's chart domain** — the deterministic identity on the selected records, the domain is the component of the
  retained domain `ℍ ∖ (K_s ∪ η[0, start])` read from the record (MARKS'
  `exists_isMeasChart_of_hasOriginalTargetRestartChart` form, `RecordDomainComponent`), gives the almost-sure physical
  form `dom_component` (`dom_component_of_record`): the record's counterflow history hull is the glued counterflow
  hull on good counterflow histories (almost surely) and the record prefix is the physical prefix (almost surely);
* **the initial data** — from PROVE-AUX61-GLUEINST's `Aux61GAlign.exists_source_initial_data` for the cut family, given
  its zero-time physical comparisons (`ZeroComparisons`).

`R1Inputs` collects what then remains; `R1Inputs.recordInputs` proves `RecordInputs` for any obstacle family with
`ObstacleFacts`, and `dyCover_of_r1`, `dyCover_of_r1_both` give the dyadic fibre cover at universes `u` and `0`;
`dyCover_of_r1_retObs_both` is the form with R1's obstacle `retObs` (its obstacle facts proved).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Asm2

open Aux61Marks Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData Aux61GInst Aux61Fib
open Aux61SlitW (SourceRestartData SourceRestartFacts SourceRecord SourceSetting SourceChartGeometry sourceChart
  sourceRecord rationalTime)
open Aux61ChLoc (IsChartGaussAt)
open GlueCond (cfHullQ)

universe u

/-! ### Almost-sure facts of a source setting -/

section Setting

variable (S : SourceSetting.{u})

/-- Almost surely the own record trace is the physical trace and the physical path is continuous. -/
theorem ae_trace_eq_and_continuous : ∀ᵐ p ∂S.μ,
    (∀ t : ℝ≥0, histTrace 0 (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) t = S.path p.1 t) ∧
      Continuous (S.path p.1) := by
  have htr := ae_histTrace_killedHistory S.own.coupling.1 S.own.trace
    (WangWu.glueMeasure_fst S.kernel S.measCounterField)
  filter_upwards [htr, S.physical_path] with p ht hg
  refine ⟨fun t => ht t (by rw [hg.1.1]; exact ENNReal.coe_lt_top), ?_⟩
  have h := hg.2.1.2.1.comp_continuous NNReal.continuous_coe fun t => (t.2 : (0 : ℝ) ≤ t)
  refine h.congr fun t => ?_
  simp only [Function.comp_apply, Real.toNNReal_coe]

/-- Almost surely the own record trace is continuous. -/
theorem ae_continuous_ownTrace : ∀ᵐ p ∂S.μ,
    Continuous (histTrace 0 (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) := by
  filter_upwards [ae_trace_eq_and_continuous S] with p hp
  rw [show histTrace 0 (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) = S.path p.1 from funext hp.1]
  exact hp.2

/-- **Almost surely the glued counterflow history is good.** -/
theorem ae_mem_goodCfSet : ∀ᵐ p ∂S.μ, p.2 ∈ CfRegQ.goodCfSet :=
  WangWu.ae_glue_snd S.measCounterField (CfRegQ.measurable_of_isCenteredCounterflowDriver S.counterflow)
    (Cond44Ref.measurable_cfHistory (Cond44Ref.isMeasurableKilledDriving_of_isCenteredCounterflowDriver S.counterflow))
    S.field_law S.kernel S.kernel_law CfRegQ.measurableSet_goodCfSet
    (CrossCond.Theta.ae_cfHistory_mem_goodCfSetT S.κ_pos S.theta_bounds S.own.coupling S.counterflow
      S.theta_field_law)

end Setting

/-- **On a good counterflow history, the record's history hull is the glued counterflow hull.** -/
theorem historyHull_stopRec_eq_cfHullQ {β : Type*} {s : ℝ≥0} {y : HistorySpace 0 0} (hy : y ∈ CfRegQ.goodCfSet)
    (g : β) :
    Aux61Restart.historyHull s (fun p : HistorySpace 0 0 × β => p.1) (stopRec s y, g) = cfHullQ s y := by
  have hst : stopRec s y = GlueCond.cfStop s y := rfl
  simp only [Aux61Restart.historyHull]
  rw [hst, CrossCond.Word49.cfDrv0_cfStop, CrossCond.Word49.fwdHull_cfDrv0 hy s,
    ← GlueCond.cfHullQ_eq_of_mem_goodCfSet hy]

/-! ### The contact rule -/

section Contact

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (C : F.ι → SourceRecord S.nL S.nR → Set ℂ)

/-- **The contact rule is the absolute contact time**: almost surely on the restart event, MARKS' contact rule of a
closed nonempty obstacle read at the restart time is `start + contact`, once the contact is the first hitting time of
the obstacle by the canonical restart path, which starts off it. -/
theorem contact_rule_of_hit (hC : ∀ i p, IsClosed (C i p)) (hCne : ∀ i p, (C i p).Nonempty)
    (hhit : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
      F.contact i p = hitTime (recordPath S (F.start i))
        (fun p => C i (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) p ∧
      recordPath S (F.start i) p 0 ∉ C i (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p))
    (i : F.ι) :
    ∀ᵐ p ∂S.μ, p ∈ F.event i →
      contactRule (C i) (F.start i) (stopRec (rationalTime S.s) p.2,
        killedHistory S.own.W S.own.VL S.own.VR S.life p.1) = (F.start i : ℝ≥0∞) + F.contact i p := by
  filter_upwards [hhit i, ae_recordPath S, ae_continuous_ownTrace S] with p hp hrp hct he
  obtain ⟨hT, h0⟩ := hp he
  rw [hT]
  exact contactRule_eq_add_hitTime (ρ := recordPath S (F.start i))
    (Y₀ := fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2)
    (R₀ := fun p => killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (x := p) (hrp (F.start i)).2.1 hct
    (hC i _) (hCne i _) h0 fun _ _ _ => rfl

/-- **R1's obstacle** (the counterflow history hull and the real line) has the obstacle properties. -/
theorem retObs_properties :
    (∀ p, IsClosed (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR) p)) ∧
      (∀ p, (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR) p).Nonempty) ∧
      ∀ z : ℂ, Measurable fun p => infDist z (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR) p) :=
  ⟨fun p => isClosed_retObs _ p, fun p => retObs_nonempty _ p, fun z => measurable_infDist_retObs _ z⟩

end Contact

/-! ### R1's chart domain -/

section Domain

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)

/-- **R1's chart domain on the selected records**: the component of the retained domain `ℍ ∖ (K_s ∪ η[0, start])`
read from the record (counterflow history hull of the record, own record prefix). -/
def RecordDomainComponent : Prop :=
  ∀ i, ∃ b : SourceRecord S.nL S.nR → ℂ, ∀ y ∈ F.selected i,
    ((F.chart i y).dom : Set ℂ) = connectedComponentIn (Aux61Restart.retainedDomain
      (Aux61Restart.historyHull (rationalTime S.s) (fun p : HistorySpace 0 0 × HistorySpace S.nL S.nR => p.1) y)
      (fun t : ℝ => histTrace 0 y.2 t.toNNReal) (F.start i)) (b y)

/-- **The physical form of R1's chart domain**: from the record identity, almost surely on the restart event the chart
domain is a component of the retained domain with the glued counterflow hull and the physical prefix. -/
theorem dom_component_of_record (hD : RecordDomainComponent S F)
    (hEv : ∀ i, F.event i =ᵐ[S.μ]
      sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i ⁻¹' F.selected i) (i : F.ι) :
    ∀ᵐ p ∂S.μ, p ∈ F.event i → ∃ b : ℂ,
      ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
        connectedComponentIn (Aux61Restart.retainedDomain (cfHullQ (rationalTime S.s) p.2)
          (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i)) b := by
  obtain ⟨b, hb⟩ := hD i
  filter_upwards [hEv i, ae_mem_goodCfSet S, ae_trace_eq_and_continuous S] with p he hy ht hE
  have hsel : sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := by
    have h : p ∈ sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i ⁻¹' F.selected i :=
      (show (p ∈ F.event i) = _ from he) ▸ hE
    exact h
  refine ⟨b (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p), ?_⟩
  have hK : Aux61Restart.historyHull (rationalTime S.s)
      (fun p : HistorySpace 0 0 × HistorySpace S.nL S.nR => p.1)
      (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) = cfHullQ (rationalTime S.s) p.2 :=
    historyHull_stopRec_eq_cfHullQ hy _
  have hη : EqOn (fun t : ℝ => histTrace 0
      (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2 t.toNNReal)
      (fun t : ℝ => S.path p.1 t.toNNReal) (Icc 0 (F.start i : ℝ)) := by
    intro v hv
    have hle : v.toNNReal ≤ F.start i := Real.toNNReal_le_iff_le_coe.2 hv.2
    simp only [sourceRecord]
    rw [histTrace_stopRec_of_le hle, ht.1]
  change ((F.chart i (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)).dom : Set ℂ) = _
  rw [hb _ hsel, hK, Aux61Restart.retainedDomain, Aux61Restart.retainedDomain, hη.image_eq]

/-- **The event facts for the selected-record event**: if each restart event is the preimage of the selected records,
it is measurable and (trivially) almost surely equal to that preimage. -/
theorem eventFacts_of_eq_preimage (hsel : ∀ i, MeasurableSet (F.selected i))
    (hE : ∀ i, F.event i = sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i ⁻¹' F.selected i) :
    (∀ i, MeasurableSet (F.event i)) ∧
      ∀ i, F.event i =ᵐ[S.μ] sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i ⁻¹' F.selected i := by
  refine ⟨fun i => ?_, fun i => by rw [hE i]⟩
  rw [hE i]
  exact Aux61SlitW.measurable_sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life
    S.own.coupling.2.2.2.1 i (hsel i)

end Domain

/-! ### The remaining inputs and the fibre cover -/

section Inputs

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (C : F.ι → SourceRecord S.nL S.nR → Set ℂ)

/-- **The per-sample restart clauses not supplied by R1's chart** (`RestartGeoPt` without the conformality and the
continuity of the lift): the path starts in the closure of the chart domain where the chart tends to `0`, stays in the
domain before the contact, the access landing, and the lift is harmonic. -/
def RestartGeoRest (i : F.ι) (p : S.Ω × HistorySpace 0 0) : Prop :=
  F.path i p 0 ∈ closure ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) ∧
  Tendsto (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).1
    (𝓝[((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ)] (F.path i p 0))
    (𝓝 0) ∧
  (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < F.contact i p →
    F.path i p u ∈ (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom) ∧
  (0 < F.contact i p →
    Aux61FibData.exitTime (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
      (F.path i) (F.contact i) (F.data i).V p = F.contact i p → F.contact i p < ⊤ →
    ∃ L : ℂ, L ∉ (F.data i).V ∧
      Tendsto (inPath (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (F.path i) (F.contact i) p) (𝓝[<] (F.contact i p).toNNReal) (𝓝 L)) ∧
  InnerProductSpace.HarmonicOnNhd (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.2
    (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom

/-- **A contact obstacle family**: closed, nonempty, with distances measurable in the records. -/
structure ObstacleFacts : Prop where
  closed : ∀ i p, IsClosed (C i p)
  nonempty : ∀ i p, (C i p).Nonempty
  measurable : ∀ i (z : ℂ), Measurable fun p => infDist z (C i p)

/-- **R1's obstacle** is a contact obstacle family. -/
theorem obstacleFacts_retObs :
    ObstacleFacts S F fun _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR) :=
  ⟨fun _ => (retObs_properties S).1, fun _ => (retObs_properties S).2.1, fun _ => (retObs_properties S).2.2⟩

/-- **The remaining physical inputs after the wiring** (owner PROVE-AUX61-GLUEINST), for a restart family `F` (event,
record chart, contact, window data; the path is the canonical record path) and a contact obstacle `C` (R1:
`retObs`, `retObs_properties`). -/
structure R1Inputs : Prop where
  selected_measurable : ∀ i, MeasurableSet (F.selected i)
  chart_measurable : ∀ i, IsMeasChart (F.chart i)
  chart_conformal : ∀ i, ∀ y ∈ F.selected i, (F.chart i y).IsConformal
  chart_lift : ∀ i, ∀ y ∈ F.selected i, ContinuousOn (F.chart i y).2.2 (F.chart i y).dom
  chart_domain : RecordDomainComponent S F
  event_measurable : ∀ i, MeasurableSet (F.event i)
  contact_measurable : ∀ i, Measurable (F.contact i)
  contact_hit : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    F.contact i p = hitTime (recordPath S (F.start i))
      (fun p => C i (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)) p ∧
    recordPath S (F.start i) p 0 ∉ C i (sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  open_window : ∀ i, IsOpen (F.data i).V
  zero_window : ∀ i, (0 : ℂ) ∈ (F.data i).V
  clearance : ∀ i, (F.data i).ℓ = clr (F.data i).V
  kappa : ∀ i, (F.data i).κ = S.κ
  reference : ∀ i, Aux61Cov.RefWin (F.data i).κ (F.data i).bR (F.data i).JR (Ioo (F.left i) (F.right i))
  event_version : ∀ i,
    F.event i =ᵐ[S.μ] sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i ⁻¹' F.selected i
  physical_stop : ∀ i, ∀ᵐ p ∂S.μ, sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      F.selected i →
    p ∈ F.event i ∧ 0 < F.contact i p ∧ (F.contact i p < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < F.contact i p ∧
      inPath (F.event i) (sourceChart (withRecordPath S F) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S F).path i) (F.contact i) p v ∉ (F.data i).V)
  geometric : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → RestartGeoRest S (withRecordPath S F) i p
  chart_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (F.start i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  comparisons : ∀ i, Nonempty (Aux61GAlign.ZeroComparisons (S.marksData (cutSource S (withRecordPath S F))) i)
  history_cover : ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i,
    sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i
  completed_window : ∀ i, ∀ᵐ p ∂S.μ,
    sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i →
    S.windowEvent p → F.contact i p < ⊤ ∧
    (∀ v : ℝ≥0, (v : ℝ≥0∞) < F.contact i p →
      inPath (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S F).path i) (F.contact i) p v ∈ (F.data i).V) ∧
    ∃ y ∈ Ioo (F.left i) (F.right i),
      Tendsto (inPath (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S F).path i) (F.contact i) p) (𝓝[<] (F.contact i p).toNNReal) (𝓝 (y : ℂ))

variable {S F C}

/-- On the restart event, almost surely the record is selected. -/
theorem R1Inputs.ae_selected (hI : R1Inputs S F C) (i : F.ι) : ∀ᵐ p ∂S.μ, p ∈ F.event i →
    sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i := by
  filter_upwards [hI.event_version i] with p he hE
  have h : p ∈ sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i ⁻¹' F.selected i :=
    (show (p ∈ F.event i) = _ from he) ▸ hE
  exact h

/-- The restart facts for the canonical path. -/
theorem R1Inputs.recordRestartFacts (hI : R1Inputs S F C) : RecordRestartFacts S F where
  selected_measurable := hI.selected_measurable
  chart_measurable := hI.chart_measurable
  event_measurable := hI.event_measurable
  contact_measurable := hI.contact_measurable
  open_window := hI.open_window
  zero_window := hI.zero_window
  clearance := hI.clearance
  kappa := hI.kappa
  reference := hI.reference
  event_version := hI.event_version
  physical_stop := hI.physical_stop
  geometric := fun i => by
    filter_upwards [hI.geometric i, hI.ae_selected i] with p hp hsel hE
    obtain ⟨hmem, hlim, hin, hland, hlh⟩ := hp hE
    exact ⟨hI.chart_conformal i _ (hsel hE), hmem, hlim, hin, hland, hI.chart_lift i _ (hsel hE), hlh⟩

/-- **`RecordInputs` from the remaining inputs**: the contact rule is MARKS' `contactRule`, R1's domain identity gives
`dom_component`, and GLUEINST's `exists_source_initial_data` gives `initial_data`. -/
theorem R1Inputs.recordInputs (hC : ObstacleFacts S F C) (hI : R1Inputs S F C) :
    RecordInputs S F fun i => contactRule (C i) (F.start i) where
  restart := hI.recordRestartFacts
  contact_measurable := fun i => measurable_contactRule (hC.measurable i) (F.start i)
  contact_galmarino := fun i => isGalmarinoRule_contactRule (C i) (F.start i)
  contact_rule := contact_rule_of_hit S F C hC.closed hC.nonempty hI.contact_hit
  dom_component := dom_component_of_record S F hI.chart_domain hI.event_version
  chart_geometry := hI.chart_geometry
  initial_data := fun i => by
    have hR' := restart_cut_of hI.recordRestartFacts.raw (path_version_withRecordPath S F)
      (dom_component_of_record S F hI.chart_domain hI.event_version)
    have hsets := sets_marks_cut_of hR' (fun i => measurable_contactRule (hC.measurable i) (F.start i))
      (fun i => isGalmarinoRule_contactRule (C i) (F.start i))
      (contact_rule_of_hit S F C hC.closed hC.nonempty hI.contact_hit) i 0
    have hret : ∀ᵐ p ∂S.μ, p ∈ (cutSource S (withRecordPath S F)).event i →
        (((S.marksData (cutSource S (withRecordPath S F))).chart i p).dom : Set ℂ) ⊆
          H \ (cfHullQ (rationalTime S.s) p.2 ∪ (fun t : ℝ => S.path p.1 t.toNNReal) '' Icc 0 (F.start i : ℝ)) := by
      filter_upwards [hI.chart_geometry i] with p hp he
      exact (hp he.1).retained
    obtain ⟨Z0⟩ := hI.comparisons i
    obtain ⟨g, hg, -, hinit⟩ :=
      Aux61GAlign.exists_source_initial_data S (cutSource S (withRecordPath S F)) hR' i hsets hret Z0
    exact ⟨g, hg, hinit⟩
  history_cover := hI.history_cover
  completed_window := hI.completed_window

end Inputs

/-! ### The fibre cover -/

/-- **Theorem 1.2's fibre leaf from the remaining inputs**: the dyadic fibre cover from restart families `F S`, contact
obstacles `C S` with `ObstacleFacts`, and `R1Inputs` in every source setting. -/
theorem dyCover_of_r1 (F : ∀ S : SourceSetting.{u}, SourceRestartData S.Ω S.nL S.nR)
    (C : ∀ S : SourceSetting.{u}, (F S).ι → SourceRecord S.nL S.nR → Set ℂ)
    (hC : ∀ S : SourceSetting.{u}, ObstacleFacts S (F S) (C S)) (hI : ∀ S : SourceSetting.{u}, R1Inputs S (F S) (C S)) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_record F (fun S i => contactRule (C S i) ((F S).start i)) fun S => (hI S).recordInputs (hC S)

/-- **The fibre cover at universes `u` and `0`** from the remaining inputs. -/
theorem dyCover_of_r1_both (F : ∀ S : SourceSetting.{u}, SourceRestartData S.Ω S.nL S.nR)
    (C : ∀ S : SourceSetting.{u}, (F S).ι → SourceRecord S.nL S.nR → Set ℂ)
    (hC : ∀ S : SourceSetting.{u}, ObstacleFacts S (F S) (C S)) (hI : ∀ S : SourceSetting.{u}, R1Inputs S (F S) (C S))
    (F₀ : ∀ S : SourceSetting.{0}, SourceRestartData S.Ω S.nL S.nR)
    (C₀ : ∀ S : SourceSetting.{0}, (F₀ S).ι → SourceRecord S.nL S.nR → Set ℂ)
    (hC₀ : ∀ S : SourceSetting.{0}, ObstacleFacts S (F₀ S) (C₀ S))
    (hI₀ : ∀ S : SourceSetting.{0}, R1Inputs S (F₀ S) (C₀ S)) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin ∧
      Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  ⟨dyCover_of_r1 F C hC hI, dyCover_of_r1 F₀ C₀ hC₀ hI₀⟩

/-- **The fibre cover at universes `u` and `0` with R1's contact obstacle** `retObs` (first contact with the
counterflow history hull or the real line): only `R1Inputs` remain. -/
theorem dyCover_of_r1_retObs_both (F : ∀ S : SourceSetting.{u}, SourceRestartData S.Ω S.nL S.nR)
    (hI : ∀ S : SourceSetting.{u}, R1Inputs S (F S) fun _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
    (F₀ : ∀ S : SourceSetting.{0}, SourceRestartData S.Ω S.nL S.nR)
    (hI₀ : ∀ S : SourceSetting.{0},
      R1Inputs S (F₀ S) fun _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin ∧
      Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_r1_both F _ (fun S => obstacleFacts_retObs S (F S)) hI F₀ _ (fun S => obstacleFacts_retObs S (F₀ S)) hI₀

end InteractingSLE.Sec5.Aux61Asm2
