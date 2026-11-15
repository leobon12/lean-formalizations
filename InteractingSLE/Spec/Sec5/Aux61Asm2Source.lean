/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Asm2Rec
import InteractingSLE.Spec.Sec5.Aux61SlitWSourceOn
import InteractingSLE.Spec.Sec5.CrossCondMartStop

/-!
# The source restart family cut down to its pointwise-good samples

Packet PROVE-AUX61-ASSEMBLE2. SLITW's `Aux61SlitW.dyCover_of_source` gives the dyadic fibre cover from a restart
family `F : SourceRestartData` in every source setting and the inputs `S.Inputs F`. Two of those inputs,
`code_marks` and `sets_marks` (MARKS' `code_le` and `baseSets_marks` for the concrete marks), need the record readings
of the restart **pointwise** on the restart event, while the physical construction supplies them almost surely.

This file closes that gap once and for all: from a raw family `F` (GLUEINST's restart objects) it builds the family
`cutSource S F`, equal to `F` except that each restart event is intersected with one measurable set of full measure,
`goodSet S F`, chosen (by `toMeasurable`) inside the set of samples at which

* the own flow's record trace is the physical trace at every time, and the physical trace is continuous;
* on every restart event, the restart path is the physical continuation before the contact, and the chart domain is
  R1's component of the retained domain `ℍ ∖ (K_s ∪ η[0, t₀])`.

Main results:
* `inPath_congr_event`, `exitTime_congr_event`: the chart path and window exit at a sample only see whether the sample
  is in the event;
* `cutEvent`, `sourceRestartFacts_cutEvent`: cutting the events by a measurable set of full measure keeps every
  restart fact;
* `GoodPt`, `goodSet`, `measurableSet_goodSet`, `goodPt_of_mem_goodSet`, `ae_mem_goodSet`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Asm2

open Aux61Marks Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData Aux61GInst Aux61Fib
open Aux61SlitW (SourceRestartData SourceRestartFacts SourceRecord SourceSetting sourceChart sourceRecord
  rationalTime)
open GlueCond (cfHullQ)

universe u

/-! ### The chart path and the window exit only see membership in the event -/

section Congr

variable {X : Type*} {E E' : Set X} {c : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ} {x : X}

/-- The chart path at a sample depends on the event only through membership of the sample. -/
theorem inPath_congr_event (h : x ∈ E ↔ x ∈ E') : inPath E c ρ T x = inPath E' c ρ T x := by
  funext u
  unfold inPath
  by_cases hx : x ∈ E
  · have hx' : x ∈ E' := h.1 hx
    simp only [hx, hx', true_and]
  · have hx' : x ∉ E' := fun h' => hx (h.2 h')
    simp only [hx, hx', false_and, ↓reduceIte]

/-- The window events at a sample depend on the event only through membership of the sample. -/
theorem mem_winEv_congr_event (h : x ∈ E ↔ x ∈ E') (a : ℝ≥0) :
    x ∈ winEv E c ρ T V a ↔ x ∈ winEv E' c ρ T V a := by
  simp only [winEv, mem_ofPred_eq, inPath_congr_event (c := c) (ρ := ρ) (T := T) h, h]

/-- The window exit at a sample depends on the event only through membership of the sample. -/
theorem exitTime_congr_event (h : x ∈ E ↔ x ∈ E') :
    Aux61FibData.exitTime E c ρ T V x = Aux61FibData.exitTime E' c ρ T V x := by
  classical
  simp only [Aux61FibData.exitTime, mem_winEv_congr_event (c := c) (ρ := ρ) (T := T) (V := V) h]

end Congr

/-! ### Cutting the restart events -/

section Cut

variable {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ}

/-- **The restart family with every event intersected with `G`** (all other objects unchanged). -/
def cutEvent (F : SourceRestartData Ω nL nR) (G : Set (Ω × HistorySpace 0 0)) : SourceRestartData Ω nL nR where
  ι := F.ι
  countable := F.countable
  start := F.start
  selected := F.selected
  chart := F.chart
  event := fun i => F.event i ∩ G
  path := F.path
  contact := F.contact
  data := F.data
  left := F.left
  right := F.right

variable (F : SourceRestartData Ω nL nR) (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
  (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  {μ : Measure (Ω × HistorySpace 0 0)} {G : Set (Ω × HistorySpace 0 0)}

omit [MeasurableSpace Ω] in
/-- The chart of the cut family is the chart of the family. -/
theorem sourceChart_cutEvent (i : F.ι) :
    sourceChart (cutEvent F G) s W VL VR ζ i = sourceChart F s W VL VR ζ i := rfl

omit [MeasurableSpace Ω] in
/-- The initial record of the cut family is the initial record of the family. -/
theorem sourceRecord_cutEvent (i : F.ι) :
    sourceRecord (cutEvent F G) s W VL VR ζ i = sourceRecord F s W VL VR ζ i := rfl

omit [MeasurableSpace Ω] in
/-- On the cut event, the chart paths of the cut family and of the family agree. -/
theorem inPath_cutEvent {i : F.ι} {x : Ω × HistorySpace 0 0} (hx : x ∈ G) (c : _ → Chart)
    (ρ : _ → ℝ≥0 → ℂ) (T : _ → ℝ≥0∞) :
    inPath ((cutEvent F G).event i) c ρ T x = inPath (F.event i) c ρ T x :=
  inPath_congr_event (by simp only [cutEvent, mem_inter_iff, hx, and_true])

omit [MeasurableSpace Ω] in
/-- On the cut event, the window exits of the cut family and of the family agree. -/
theorem exitTime_cutEvent {i : F.ι} {x : Ω × HistorySpace 0 0} (hx : x ∈ G) (c : _ → Chart)
    (ρ : _ → ℝ≥0 → ℂ) (T : _ → ℝ≥0∞) (V : Set ℂ) :
    Aux61FibData.exitTime ((cutEvent F G).event i) c ρ T V x = Aux61FibData.exitTime (F.event i) c ρ T V x :=
  exitTime_congr_event (by simp only [cutEvent, mem_inter_iff, hx, and_true])

/-- **Cutting the events by a measurable set of full measure keeps every restart fact.** -/
theorem sourceRestartFacts_cutEvent {κ : ℝ} (hR : SourceRestartFacts F s W VL VR ζ (μ := μ) κ)
    (hG : MeasurableSet G) (hGae : ∀ᵐ p ∂μ, p ∈ G) :
    SourceRestartFacts (cutEvent F G) s W VL VR ζ (μ := μ) κ := by
  refine
    { selected_measurable := hR.selected_measurable
      chart_measurable := hR.chart_measurable
      spec := fun i => ?_
      open_window := hR.open_window
      zero_window := hR.zero_window
      landing := fun i => ?_
      injective_path := fun i x hx => hR.injective_path i x hx.1
      continuous_lift := fun i x hx => hR.continuous_lift i x hx.1
      harmonic_lift := fun i x hx => hR.harmonic_lift i x hx.1
      clearance := hR.clearance
      kappa := hR.kappa
      reference := hR.reference
      event_version := fun i => ?_
      physical_stop := fun i => ?_ }
  · have hs := hR.spec i
    exact
      { measurableSet := hs.measurableSet.inter hG
        measT := hs.measT
        measρ := hs.measρ
        contρ := fun x hx => hs.contρ x hx.1
        chart := hs.chart
        conf := fun x hx => hs.conf x hx.1
        start_mem := fun x hx => hs.start_mem x hx.1
        start_lim := fun x hx => hs.start_lim x hx.1
        inside := fun x hx => hs.inside x hx.1 }
  · intro x hx hT hexit hfin
    rw [exitTime_cutEvent F (i := i) hx.2] at hexit
    obtain ⟨L, hL, hlim⟩ := hR.landing i x hx.1 hT hexit hfin
    exact ⟨L, hL, by rw [inPath_cutEvent F (i := i) hx.2]; exact hlim⟩
  · refine EventuallyEq.trans ?_ (hR.event_version i)
    filter_upwards [hGae] with p hp
    simp only [cutEvent, mem_inter_iff, hp, and_true]
  · filter_upwards [hR.physical_stop i, hGae] with p hp hpG hsel
    obtain ⟨hE, hpos, hstop⟩ := hp hsel
    refine ⟨⟨hE, hpG⟩, hpos, ?_⟩
    rcases hstop with hfin | ⟨v, hv, hout⟩
    · exact Or.inl hfin
    · exact Or.inr ⟨v, hv, by rw [inPath_cutEvent F (i := i) hpG]; exact hout⟩

end Cut

/-! ### The pointwise-good samples of a source setting -/

section Good

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)

/-- **The pointwise restart facts** of the restart `i` at the sample `p` (the clauses of `IsRestartSpec`,
`HasAccessLanding`, the injectivity of the path and R1's lift that concern one sample). -/
def RestartPt (i : F.ι) (p : S.Ω × HistorySpace 0 0) : Prop :=
  Continuous (F.path i p) ∧
  (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).IsConformal ∧
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
  InjOn (F.path i p) {u | (u : ℝ≥0∞) < F.contact i p} ∧
  ContinuousOn (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.2
    (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom ∧
  InnerProductSpace.HarmonicOnNhd (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.2
    (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom

/-- **The pointwise-good samples**: the own flow's record trace is the physical trace at every time, the physical trace
is continuous, and on every restart event the restart path is the physical continuation before the contact, the chart
domain is a component of the retained domain `ℍ ∖ (K_s ∪ η[0, t₀])`, and the pointwise restart facts hold. -/
def GoodPt (p : S.Ω × HistorySpace 0 0) : Prop :=
  (∀ t : ℝ≥0, histTrace 0 (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) t = S.path p.1 t) ∧
  ContinuousOn (fun t : ℝ => S.path p.1 t.toNNReal) (Ici 0) ∧
  ∀ i, p ∈ F.event i →
    (∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < F.contact i p → F.path i p v = S.path p.1 (F.start i + v)) ∧
    (∃ b : ℂ, ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
      connectedComponentIn (Aux61Restart.retainedDomain (cfHullQ (rationalTime S.s) p.2)
        (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i)) b) ∧
    RestartPt S F i p

/-- **The good set**: a measurable set of samples, all pointwise good, of full measure as soon as almost every sample
is good (the complement of a measurable hull of the bad samples). -/
def goodSet : Set (S.Ω × HistorySpace 0 0) := (toMeasurable S.μ {p | ¬ GoodPt S F p})ᶜ

theorem measurableSet_goodSet : MeasurableSet (goodSet S F) := (measurableSet_toMeasurable _ _).compl

theorem goodPt_of_mem_goodSet {p : S.Ω × HistorySpace 0 0} (hp : p ∈ goodSet S F) : GoodPt S F p := by
  by_contra hn
  exact hp (subset_toMeasurable _ _ hn)

theorem ae_mem_goodSet (h : ∀ᵐ p ∂S.μ, GoodPt S F p) : ∀ᵐ p ∂S.μ, p ∈ goodSet S F := by
  rw [ae_iff] at h ⊢
  have e : {p | ¬ p ∈ goodSet S F} = toMeasurable S.μ {p | ¬ GoodPt S F p} := by
    ext p
    simp only [goodSet, mem_compl_iff, not_not, mem_ofPred_eq]
  rw [e, measure_toMeasurable]
  exact h

/-- **Almost every sample is good** once the restart paths are almost surely the physical continuations and the chart
domains almost surely components of the retained domains, on the restart events (the trace facts come from the flow
line). -/
theorem ae_goodPt
    (hpath : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∀ v : ℝ≥0, 0 < v →
      (v : ℝ≥0∞) < F.contact i p → F.path i p v = S.path p.1 (F.start i + v))
    (hdom : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∃ b : ℂ,
      ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
        connectedComponentIn (Aux61Restart.retainedDomain (cfHullQ (rationalTime S.s) p.2)
          (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i)) b)
    (hreg : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → RestartPt S F i p) :
    ∀ᵐ p ∂S.μ, GoodPt S F p := by
  have htr := ae_histTrace_killedHistory S.own.coupling.1 S.own.trace
    (WangWu.glueMeasure_fst S.kernel S.measCounterField)
  filter_upwards [htr, S.physical_path, ae_all_iff.2 hpath, ae_all_iff.2 hdom, ae_all_iff.2 hreg]
    with p ht hg hpa hd hr
  exact ⟨fun t => ht t (by rw [hg.1.1]; exact ENNReal.coe_lt_top), hg.2.1.2.1,
    fun i hi => ⟨hpa i hi, hd i hi, hr i hi⟩⟩

/-- **The source family cut down to the good samples.** -/
abbrev cutSource : SourceRestartData S.Ω S.nL S.nR := cutEvent F (goodSet S F)

/-- A sample of a cut restart event is good. -/
theorem goodPt_of_mem_cut {i : F.ι} {p : S.Ω × HistorySpace 0 0} (hp : p ∈ (cutSource S F).event i) :
    GoodPt S F p := goodPt_of_mem_goodSet S F hp.2

/-- On a cut restart event the restart path is the own record trace before the contact. -/
theorem path_read_of_mem_cut {i : F.ι} {p : S.Ω × HistorySpace 0 0} (hp : p ∈ (cutSource S F).event i)
    (v : ℝ≥0) (hv : 0 < v) (hvT : (v : ℝ≥0∞) < F.contact i p) :
    F.path i p v = histTrace 0 (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (F.start i + v) := by
  have hg := goodPt_of_mem_cut S F hp
  rw [(hg.2.2 i hp.1).1 v hv hvT, hg.1]

/-- On a cut restart event the time-`t₀` record trace is the physical trace on `[0, t₀]`. -/
theorem stoppedTrace_eqOn_of_mem_cut {i : F.ι} {p : S.Ω × HistorySpace 0 0} (hp : p ∈ (cutSource S F).event i) :
    EqOn (fun v : ℝ => histTrace 0 (stopRec (F.start i) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))
      v.toNNReal) (fun t : ℝ => S.path p.1 t.toNNReal) (Icc 0 (F.start i : ℝ)) := by
  intro v hv
  have hle : v.toNNReal ≤ F.start i := Real.toNNReal_le_iff_le_coe.2 hv.2
  simp only
  rw [histTrace_stopRec_of_le hle, (goodPt_of_mem_cut S F hp).1]

/-- On a cut restart event the chart domain is a component of the retained domain read from the time-`t₀` record. -/
theorem dom_read_of_mem_cut {i : F.ι} {p : S.Ω × HistorySpace 0 0} (hp : p ∈ (cutSource S F).event i) :
    ∃ b : ℂ, ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
      connectedComponentIn (Aux61Restart.retainedDomain (cfHullQ (rationalTime S.s) p.2)
        (fun v : ℝ => histTrace 0 (stopRec (F.start i) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))
          v.toNNReal) (F.start i)) b := by
  obtain ⟨b, hb⟩ := ((goodPt_of_mem_cut S F hp).2.2 i hp.1).2.1
  refine ⟨b, ?_⟩
  rw [hb, Aux61Restart.retainedDomain, Aux61Restart.retainedDomain,
    (stoppedTrace_eqOn_of_mem_cut S F hp).image_eq]

/-- On a cut restart event the time-`t₀` record trace is continuous on `[0, t₀]`. -/
theorem continuousOn_stoppedTrace_of_mem_cut {i : F.ι} {p : S.Ω × HistorySpace 0 0}
    (hp : p ∈ (cutSource S F).event i) :
    ContinuousOn (fun v : ℝ => histTrace 0 (stopRec (F.start i) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))
      v.toNNReal) (Icc 0 (F.start i : ℝ)) :=
  ((goodPt_of_mem_cut S F hp).2.1.mono fun _ hv => hv.1).congr (stoppedTrace_eqOn_of_mem_cut S F hp)

/-- On a cut restart event the pointwise restart facts hold. -/
theorem restartPt_of_mem_cut {i : F.ι} {p : S.Ω × HistorySpace 0 0} (hp : p ∈ (cutSource S F).event i) :
    RestartPt S F i p := ((goodPt_of_mem_cut S F hp).2.2 i hp.1).2.2

/-- **The restart/window facts of a raw family, with every per-sample clause asked only almost surely on the
event** (the pointwise clauses of `SourceRestartFacts` are collected in `RestartPt`). -/
structure RawRestartFacts : Prop where
  selected_measurable : ∀ i, MeasurableSet (F.selected i)
  chart_measurable : ∀ i, IsMeasChart (F.chart i)
  event_measurable : ∀ i, MeasurableSet (F.event i)
  contact_measurable : ∀ i, Measurable (F.contact i)
  path_measurable : ∀ i (u : ℝ≥0), Measurable fun p => F.path i p u
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
      inPath (F.event i) (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i) (F.path i)
        (F.contact i) p v ∉ (F.data i).V)
  regular : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → RestartPt S F i p

/-- SLITW's (pointwise) restart facts give the raw ones. -/
theorem RawRestartFacts.of_sourceRestartFacts
    (hR : SourceRestartFacts F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ) :
    RawRestartFacts S F where
  selected_measurable := hR.selected_measurable
  chart_measurable := hR.chart_measurable
  event_measurable := fun i => (hR.spec i).measurableSet
  contact_measurable := fun i => (hR.spec i).measT
  path_measurable := fun i => (hR.spec i).measρ
  open_window := hR.open_window
  zero_window := hR.zero_window
  clearance := hR.clearance
  kappa := hR.kappa
  reference := hR.reference
  event_version := hR.event_version
  physical_stop := hR.physical_stop
  regular := fun i => Eventually.of_forall fun p hp =>
    ⟨(hR.spec i).contρ p hp, (hR.spec i).conf p hp, (hR.spec i).start_mem p hp, (hR.spec i).start_lim p hp,
      (hR.spec i).inside p hp, hR.landing i p hp, hR.injective_path i p hp, hR.continuous_lift i p hp,
      hR.harmonic_lift i p hp⟩

/-- **The cut family has SLITW's restart facts** once the raw facts hold and almost every sample is good. -/
theorem sourceRestartFacts_cut_of_raw (hR : RawRestartFacts S F) (hgood : ∀ᵐ p ∂S.μ, p ∈ goodSet S F) :
    SourceRestartFacts (cutSource S F) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life (μ := S.μ) S.κ := by
  have hX := S.own.coupling.2.2.2.1
  have hcm : ∀ i, IsMeasChart (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i) := by
    intro i
    have hm := Aux61SlitW.measurable_sourceRecord F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life hX i
    exact ⟨fun z => hm ((hR.chart_measurable i).dom z), fun z => ((hR.chart_measurable i).fwd z).comp hm,
      fun z => ((hR.chart_measurable i).lift z).comp hm⟩
  refine
    { selected_measurable := hR.selected_measurable
      chart_measurable := hR.chart_measurable
      spec := fun i =>
        { measurableSet := (hR.event_measurable i).inter (measurableSet_goodSet S F)
          measT := hR.contact_measurable i
          measρ := hR.path_measurable i
          contρ := fun x hx => (restartPt_of_mem_cut S F hx).1
          chart := hcm i
          conf := fun x hx => (restartPt_of_mem_cut S F hx).2.1
          start_mem := fun x hx => (restartPt_of_mem_cut S F hx).2.2.1
          start_lim := fun x hx => (restartPt_of_mem_cut S F hx).2.2.2.1
          inside := fun x hx => (restartPt_of_mem_cut S F hx).2.2.2.2.1 }
      open_window := hR.open_window
      zero_window := hR.zero_window
      landing := fun i x hx hT hexit hfin => ?_
      injective_path := fun i x hx => (restartPt_of_mem_cut S F hx).2.2.2.2.2.2.1
      continuous_lift := fun i x hx => (restartPt_of_mem_cut S F hx).2.2.2.2.2.2.2.1
      harmonic_lift := fun i x hx => (restartPt_of_mem_cut S F hx).2.2.2.2.2.2.2.2
      clearance := hR.clearance
      kappa := hR.kappa
      reference := hR.reference
      event_version := fun i => ?_
      physical_stop := fun i => ?_ }
  · rw [exitTime_cutEvent F (i := i) hx.2] at hexit
    obtain ⟨L, hL, hlim⟩ := (restartPt_of_mem_cut S F hx).2.2.2.2.2.1 hT hexit hfin
    exact ⟨L, hL, by rw [inPath_cutEvent F (i := i) hx.2]; exact hlim⟩
  · refine EventuallyEq.trans ?_ (hR.event_version i)
    filter_upwards [hgood] with p hp
    simp only [cutSource, cutEvent, mem_inter_iff, hp, and_true]
  · filter_upwards [hR.physical_stop i, hgood] with p hp hpG hsel
    obtain ⟨hE, hpos, hstop⟩ := hp hsel
    refine ⟨⟨hE, hpG⟩, hpos, ?_⟩
    rcases hstop with hfin | ⟨v, hv, hout⟩
    · exact Or.inl hfin
    · exact Or.inr ⟨v, hv, by rw [inPath_cutEvent F (i := i) hpG]; exact hout⟩

end Good

end InteractingSLE.Sec5.Aux61Asm2
