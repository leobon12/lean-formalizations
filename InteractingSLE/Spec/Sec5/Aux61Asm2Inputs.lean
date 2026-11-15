/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Asm2Source
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceRecord

/-!
# SLITW's source inputs for the cut restart family, and the fibre cover at universes `u` and `0`

Packet PROVE-AUX61-ASSEMBLE2. For a raw restart family `F` in a source setting `S` (GLUEINST's restart objects) and an
absolute contact rule `Ta` of the records, `RawInputs S F Ta` lists the still-open physical inputs, each almost surely
on the restart events where the source states it:

* `restart` — the restart/window facts of `F` (`RawRestartFacts`: SLITW's `SourceRestartFacts` with every per-sample
  clause asked almost surely on the event; `RawRestartFacts.of_sourceRestartFacts` converts the pointwise form);
* `contact_measurable`, `contact_galmarino`, `contact_rule` — the absolute contact time `start + contact` is a
  measurable Galmarino rule of the records (a first hit of the closed contact set);
* `path_version` — the restart path is the physical continuation `η(start + ·)` before the contact;
* `dom_component` — the chart domain is a component of the retained domain `ℍ ∖ (K_s ∪ η[0, start])` (R1);
* `chart_geometry` — R1's original-target chart geometry (`SourceChartGeometry`);
* `initial_data` — the time-`0` Gaussian decomposition with its window data, for the cut family;
* `history_cover`, `completed_window` — the countable capture of the restart-window event.

**`inputs_cutSource`** proves `S.Inputs (cutSource S F)` from them: SLITW's `code_marks` (MARKS' `code_le`, via
`Aux61Asm2.codeFiltration_le_nullRuleMarks_on`) and `sets_marks` (MARKS' `baseSets_marks` for the live chart set, via
`Aux61Asm2.measurable_liveChartSet_nullRuleMarks`) are **proved**, with the pointwise record readings supplied by the
good set; the restart facts are transferred to the cut events. **`dyCover_of_raw`** then gives the dyadic fibre cover
`DyActFibreCoverOn (¬ IsLargeGap) RefWin` through SLITW's `dyCover_of_source`, at every universe;
`dyCover_of_raw_both` packages universes `u` and `0` (the binders `hDy`, `hDy0` of the Theorem 1.2–1.3 tops).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Asm2

open Aux61Marks Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData Aux61GInst Aux61Fib
open Aux61SlitW (SourceRestartData SourceRestartFacts SourceRecord SourceSetting SourceChartGeometry sourceChart
  sourceRecord rationalTime capacityRule)
open Aux61ChLoc (IsChartGaussAt)
open GlueCond (cfHullQ)

universe u

section Inputs

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (Ta : F.ι → SourceRecord S.nL S.nR → ℝ≥0∞)

/-- **The still-open physical inputs for a raw restart family** (owners: PROVE-AUX61-GLUEINST for all fields; see the
module docstring). Every field is a fact of the source's restart construction, stated where the source states it. -/
structure RawInputs : Prop where
  restart : RawRestartFacts S F
  contact_measurable : ∀ i, Measurable (Ta i)
  contact_galmarino : ∀ i, IsGalmarinoRule stopRec (Ta i)
  contact_rule : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    Ta i (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
      (F.start i : ℝ≥0∞) + F.contact i p
  path_version : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ v : ℝ≥0, 0 < v →
    (v : ℝ≥0∞) < F.contact i p → F.path i p v = S.path p.1 (F.start i + v)
  dom_component : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∃ b : ℂ,
    ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
      connectedComponentIn (Aux61Restart.retainedDomain (cfHullQ (rationalTime S.s) p.2)
        (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i)) b
  chart_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (F.start i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  initial_data : ∀ i, ∃ g : S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
    IsChartGaussAt S.μ ((S.marksData (cutSource S F)).Z i) ((S.marksData (cutSource S F)).B i)
      ((S.marksData (cutSource S F)).code i) 0 ((S.marksData (cutSource S F)).sigma i 0) g ∧
      Nonempty (Aux61GCont.InitialWindowData (S.Ω × HistorySpace 0 0)
        (S.μ.restrict ((S.marksData (cutSource S F)).Z i ⁻¹' (S.marksData (cutSource S F)).B i)) (F.data i) g)
  history_cover : ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i,
    sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i
  completed_window : ∀ i, ∀ᵐ p ∂S.μ,
    sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ F.selected i →
    S.windowEvent p → F.contact i p < ⊤ ∧
    (∀ v : ℝ≥0, (v : ℝ≥0∞) < F.contact i p →
      inPath (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (F.path i) (F.contact i) p v ∈ (F.data i).V) ∧
    ∃ y ∈ Ioo (F.left i) (F.right i),
      Tendsto (inPath (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        (F.path i) (F.contact i) p) (𝓝[<] (F.contact i p).toNNReal) (𝓝 (y : ℂ))

/-- The completed rule marks of the restart `i` at fibre time `q` (the marks of `S.marksData`). -/
abbrev cutMarks (i : F.ι) (q : ℝ≥0) : MeasurableSpace (S.Ω × HistorySpace 0 0) :=
  nullMarks (ruleMarks stopRec (capacityRule (F.chart i) (F.start i) q)
    (fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2)
    (fun p => killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) S.μ

variable {S F Ta}

/-- **The cut family has SLITW's restart facts** once the raw restart facts hold and the restart paths and chart
domains are almost surely the physical ones on the events. -/
theorem restart_cut_of (hR : RawRestartFacts S F)
    (hpath : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ v : ℝ≥0, 0 < v →
      (v : ℝ≥0∞) < F.contact i p → F.path i p v = S.path p.1 (F.start i + v))
    (hdom : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∃ b : ℂ,
      ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
        connectedComponentIn (Aux61Restart.retainedDomain (cfHullQ (rationalTime S.s) p.2)
          (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i)) b) :
    SourceRestartFacts (cutSource S F) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ :=
  sourceRestartFacts_cut_of_raw S F hR (ae_mem_goodSet S F (ae_goodPt S F hpath hdom hR.regular))

/-- Almost every sample is in the good set. -/
theorem RawInputs.ae_good (hI : RawInputs S F Ta) : ∀ᵐ p ∂S.μ, p ∈ goodSet S F :=
  ae_mem_goodSet S F (ae_goodPt S F hI.path_version hI.dom_component hI.restart.regular)

/-- The restart facts of the cut family. -/
theorem RawInputs.restart_cut (hI : RawInputs S F Ta) :
    SourceRestartFacts (cutSource S F) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ :=
  restart_cut_of hI.restart hI.path_version hI.dom_component

/-- The initial records are measurable on the glued space. -/
theorem measurable_initialRecords :
    Measurable (fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2) ∧
      Measurable (fun p : S.Ω × HistorySpace 0 0 => killedHistory S.own.W S.own.VL S.own.VR S.life p.1) :=
  ⟨isRecordStop_stopRec.measurable.comp (measurable_const.prodMk measurable_snd),
    (measurable_killedHistory S.own.coupling.2.2.2.1).comp measurable_fst⟩

/-- **SLITW's `code_marks` for the cut family** (MARKS' `code_le`), from the cut restart facts and the contact rule. -/
theorem code_marks_cut_of
    (hR : SourceRestartFacts (cutSource S F) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ)
    (hTam : ∀ i, Measurable (Ta i)) (hTaG : ∀ i, IsGalmarinoRule stopRec (Ta i))
    (hTa : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
      Ta i (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
        (F.start i : ℝ≥0∞) + F.contact i p)
    (i : (cutSource S F).ι) (q : ℝ≥0) :
    (Aux61FibK.codeFiltration.{u} q).comap (fun p => ULift.up.{u} ((S.marksData (cutSource S F)).code i p)) ≤
      (S.marksData (cutSource S F)).baseMarks i q := by
  exact codeFiltration_le_nullRuleMarks_on (hR.spec i) (hR.open_window i) (hR.zero_window i) (hR.landing i)
    (hR.injective_path i) (hR.chart_measurable i) (hTam i) (hTaG i)
    (hR.continuous_lift i) (S.own.coupling.2.1.comp measurable_fst) (F.data i) rfl (hR.clearance i) q
    (Aux61SlitW.sourceEvent_marks (cutSource S F) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hR i q)
    (Eventually.of_forall fun _ => rfl)
    (Eventually.of_forall fun _ hp v hv hvT => path_read_of_mem_cut S F hp v hv hvT)
    (by filter_upwards [hTa i] with p hp he; exact hp he.1)
    (S.exit_on_event (cutSource S F) hR i)

/-- **SLITW's `sets_marks` for the cut family** (MARKS' `baseSets_marks` for the live chart set), from the cut restart
facts and the contact rule. -/
theorem sets_marks_cut_of
    (hR : SourceRestartFacts (cutSource S F) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ)
    (hTam : ∀ i, Measurable (Ta i)) (hTaG : ∀ i, IsGalmarinoRule stopRec (Ta i))
    (hTa : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
      Ta i (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
        (F.start i : ℝ≥0∞) + F.contact i p)
    (i : (cutSource S F).ι) (q : ℝ≥0) :
    Measurable[(S.marksData (cutSource S F)).baseMarks i q, hittingSigma]
      ((S.marksData (cutSource S F)).baseSets i q) := by
  classical
  obtain ⟨hY₀, hR₀⟩ := measurable_initialRecords (S := S)
  have hrule : ruleMarks stopRec (capacityRule (F.chart i) (F.start i) q)
      (fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2)
      (fun p => killedHistory S.own.W S.own.VL S.own.VR S.life p.1) ≤ cutMarks S F i q :=
    le_nullMarks (ruleMarks_le isRecordStop_stopRec
      (Aux61SlitW.measurable_capacityRule (hR.chart_measurable i) (F.start i) q) hY₀ hR₀)
  have hY₀m : Measurable[cutMarks S F i q] fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2 := by
    have h := measurable_ruleMarks_of_time0 (Y₀ := fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2)
      (R₀ := fun p => killedHistory S.own.W S.own.VL S.own.VR S.life p.1) measurable_fst isRecordStop_stopRec
      (Aux61SlitW.start_le_capacityRule (F.chart i) (F.start i) q)
    exact h.mono hrule le_rfl
  have hK : Measurable[cutMarks S F i q, hittingSigma]
      fun p : S.Ω × HistorySpace 0 0 => cfHullQ (rationalTime S.s) p.2 := by
    have e : (fun p : S.Ω × HistorySpace 0 0 => cfHullQ (rationalTime S.s) p.2) =
        fun p => cfHullQ (rationalTime S.s) (stopRec (rationalTime S.s) p.2) :=
      funext fun p => (CrossCond.Word49.cfHullQ_cfStop (rationalTime S.s) p.2).symm
    rw [e]
    exact (GlueCond.measurable_cfHullQ (rationalTime S.s)).comp hY₀m
  have hηm : ∀ v : ℝ, Measurable[cutMarks S F i q] fun p : S.Ω × HistorySpace 0 0 =>
      histTrace 0 (stopRec (F.start i) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) v.toNNReal := by
    intro v
    have h := measurable_ruleMarks_of_time0 (Y₀ := fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2)
      (R₀ := fun p => killedHistory S.own.W S.own.VL S.own.VR S.life p.1)
      ((measurable_histTrace (nL := S.nL) (nR := S.nR) 0 v.toNNReal).comp measurable_snd) isRecordStop_stopRec
      (Aux61SlitW.start_le_capacityRule (F.chart i) (F.start i) q)
    exact h.mono hrule le_rfl
  have hZB : MeasurableSet[cutMarks S F i q]
      ((S.marksData (cutSource S F)).Z i ⁻¹' (S.marksData (cutSource S F)).B i) :=
    hrule _ ((Aux61SlitW.sourceRecord_ruleMarks (cutSource S F) (rationalTime S.s) S.own.W S.own.VL S.own.VR
      S.life i q) (hR.selected_measurable i))
  have hb : ∀ p ∈ (cutSource S F).event i, ∃ b : ℂ,
      ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
        connectedComponentIn (Aux61Restart.retainedDomain (cfHullQ (rationalTime S.s) p.2)
          (fun v : ℝ => histTrace 0 (stopRec (F.start i) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))
            v.toNNReal) (F.start i)) b := fun p hp => dom_read_of_mem_cut S F hp
  let b : S.Ω × HistorySpace 0 0 → ℂ := fun p =>
    if hp : p ∈ (cutSource S F).event i then Classical.choose (hb p hp) else 0
  exact measurable_liveChartSet_nullRuleMarks (hR.spec i) (hR.open_window i) (hR.zero_window i) (hR.landing i)
    (hR.injective_path i) (hR.chart_measurable i) (hTam i) (hTaG i)
    (hR.continuous_lift i) (S.own.coupling.2.1.comp measurable_fst) (F.data i) rfl (hR.clearance i) hY₀ hR₀ q
    hZB (Aux61SlitW.sourceEvent_marks (cutSource S F) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hR i q)
    (fun _ => rfl) (fun _ hp v hv hvT => path_read_of_mem_cut S F hp v hv hvT)
    (by filter_upwards [hTa i] with p hp he; exact hp he.1)
    (S.exit_on_event (cutSource S F) hR i) hK (fun _ hp => continuousOn_stoppedTrace_of_mem_cut S F hp) hηm
    (b := b) fun p hp => by
      simp only [b, hp, ↓reduceDIte]
      exact Classical.choose_spec (hb p hp)

/-- **SLITW's `code_marks` for the cut family** (MARKS' `code_le`). -/
theorem RawInputs.code_marks_cut (hI : RawInputs S F Ta) (i : (cutSource S F).ι) (q : ℝ≥0) :
    (Aux61FibK.codeFiltration.{u} q).comap (fun p => ULift.up.{u} ((S.marksData (cutSource S F)).code i p)) ≤
      (S.marksData (cutSource S F)).baseMarks i q :=
  code_marks_cut_of hI.restart_cut hI.contact_measurable hI.contact_galmarino hI.contact_rule i q

/-- **SLITW's `sets_marks` for the cut family** (MARKS' `baseSets_marks` for the live chart set). -/
theorem RawInputs.sets_marks_cut (hI : RawInputs S F Ta) (i : (cutSource S F).ι) (q : ℝ≥0) :
    Measurable[(S.marksData (cutSource S F)).baseMarks i q, hittingSigma]
      ((S.marksData (cutSource S F)).baseSets i q) :=
  sets_marks_cut_of hI.restart_cut hI.contact_measurable hI.contact_galmarino hI.contact_rule i q

/-- **SLITW's source inputs for the cut family**, from the raw physical inputs. -/
theorem RawInputs.inputs_cut (hI : RawInputs S F Ta) : S.Inputs (cutSource S F) where
  restart := hI.restart_cut
  code_marks := hI.code_marks_cut
  sets_marks := hI.sets_marks_cut
  chart_geometry := fun i => by
    filter_upwards [hI.chart_geometry i] with p hp he
    exact hp he.1
  path_version := fun i => by
    filter_upwards [hI.path_version i] with p hp he
    exact hp he.1
  initial_data := hI.initial_data
  history_cover := hI.history_cover
  completed_window := fun i => by
    filter_upwards [hI.completed_window i, hI.ae_good] with p hp hpG hsel hwin
    obtain ⟨hfin, hin, y, hy, hlim⟩ := hp hsel hwin
    refine ⟨hfin, fun v hv => ?_, y, hy, ?_⟩
    · rw [inPath_cutEvent F (i := i) hpG]
      exact hin v hv
    · rw [inPath_cutEvent F (i := i) hpG]
      exact hlim

end Inputs

/-! ### The fibre cover -/

/-- **Theorem 1.2's fibre leaf from the raw restart families**: the corrected dyadic fibre cover in every small-gap
window setting, from a raw restart family `F S` and an absolute contact rule `Ta S` in every source setting with the
named physical inputs `RawInputs` (all owned by PROVE-AUX61-GLUEINST). Universe-polymorphic. -/
theorem dyCover_of_raw (F : ∀ S : SourceSetting.{u}, SourceRestartData S.Ω S.nL S.nR)
    (Ta : ∀ S : SourceSetting.{u}, (F S).ι → SourceRecord S.nL S.nR → ℝ≥0∞)
    (hI : ∀ S : SourceSetting.{u}, RawInputs S (F S) (Ta S)) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  Aux61SlitW.dyCover_of_source (fun S => cutSource S (F S)) fun S => (hI S).inputs_cut

/-- **The fibre cover at universes `u` and `0`** (the binders `hDy` and `hDy0` of `Wire.T12Asm2`'s tops), from the raw
restart families and their inputs at both universes. -/
theorem dyCover_of_raw_both (F : ∀ S : SourceSetting.{u}, SourceRestartData S.Ω S.nL S.nR)
    (Ta : ∀ S : SourceSetting.{u}, (F S).ι → SourceRecord S.nL S.nR → ℝ≥0∞)
    (hI : ∀ S : SourceSetting.{u}, RawInputs S (F S) (Ta S))
    (F₀ : ∀ S : SourceSetting.{0}, SourceRestartData S.Ω S.nL S.nR)
    (Ta₀ : ∀ S : SourceSetting.{0}, (F₀ S).ι → SourceRecord S.nL S.nR → ℝ≥0∞)
    (hI₀ : ∀ S : SourceSetting.{0}, RawInputs S (F₀ S) (Ta₀ S)) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin ∧
      Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  ⟨dyCover_of_raw F Ta hI, dyCover_of_raw F₀ Ta₀ hI₀⟩

end InteractingSLE.Sec5.Aux61Asm2
