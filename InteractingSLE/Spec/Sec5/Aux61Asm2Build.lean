/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Asm2R1

/-!
# The restart family built from R1's chart: the chart, event and contact fields closed

Packet PROVE-AUX61-ASSEMBLE2 (third round). `R1Restart S` collects the restart choices of a source setting `S`: a
countable index, rational restart times `q`, selected initial records, window data, and R1's chart data
`(r, U, e, Y, η)`
(the records read through `Y`, `η`; on the selected records `Y` is the counterflow record and `η` the own record
prefix). Under R1's existence statement `HasChart` (`Aux61Restart.HasOriginalTargetRestartChart` for every index),
`R1Restart.src` is the restart family with

* the restart time `rationalTime (q i)`;
* the chart chosen from PROVE-AUX61-MARKS' `exists_isMeasChart_of_hasOriginalTargetRestartChart` (measurable,
  conformal, continuous lift, domain the component of the retained domain);
* the event: the selected-record preimage;
* the contact: MARKS' contact rule of R1's obstacle `retObs` minus the restart time.

`R1RestartInputs.r1Inputs` proves `R1Inputs` for it: the four chart fields, the two event fields, the contact's
measurability and its identification with the first hit of the obstacle are proved; `dyCover_of_r1Restart_both` gives
the dyadic fibre cover at universes `u` and `0`.
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
open GlueCond (cfHullQ)

universe u

/-- **The restart choices of a source setting** (owner PROVE-AUX61-GLUEINST): countable index, rational restart times,
selected initial records, window data, and R1's chart data. -/
structure R1Restart (S : SourceSetting.{u}) where
  ι : Type
  [countable : Countable ι]
  q : ι → ℚ
  selected : ι → Set (SourceRecord S.nL S.nR)
  data : ι → FibData
  left : ι → ℝ
  right : ι → ℝ
  r : ι → ℝ≥0
  U : ι → ℝ≥0 → SourceRecord S.nL S.nR → ℝ
  e : ℕ → ℂ
  Y : ι → SourceRecord S.nL S.nR → HistorySpace 0 0
  η : ι → SourceRecord S.nL S.nR → ℝ → ℂ

attribute [instance] R1Restart.countable

namespace R1Restart

variable {S : SourceSetting.{u}} (D : R1Restart S)

/-- **R1's chart existence** for every index (on the record space). -/
def HasChart : Prop :=
  ∀ i, Aux61Restart.HasOriginalTargetRestartChart (rationalTime S.s) (D.r i) (D.q i) (D.Y i) (D.η i) (D.U i) D.e

/-- **R1's chart family** chosen from MARKS' `exists_isMeasChart_of_hasOriginalTargetRestartChart`. -/
def chart (h : D.HasChart) (i : D.ι) : SourceRecord S.nL S.nR → Chart :=
  Classical.choose (Classical.choose_spec (exists_isMeasChart_of_hasOriginalTargetRestartChart (h i))).2.2

/-- The facts of R1's chart family. -/
theorem chart_spec (h : D.HasChart) (i : D.ι) :
    IsMeasChart (D.chart h i) ∧ (∀ y, (D.chart h i y).IsConformal) ∧
      (∃ b : SourceRecord S.nL S.nR → ℂ, ∀ y, ((D.chart h i y).dom : Set ℂ) =
        connectedComponentIn (Aux61Restart.retainedDomain (Aux61Restart.historyHull (rationalTime S.s) (D.Y i) y)
          (D.η i y) (D.q i)) (b y)) ∧
      ∀ y, ContinuousOn (D.chart h i y).2.2 (D.chart h i y).dom := by
  have hex := exists_isMeasChart_of_hasOriginalTargetRestartChart (h i)
  have hc := Classical.choose_spec (Classical.choose_spec hex).2.2
  exact ⟨hc.1, hc.2.1, ⟨Classical.choose hex, hc.2.2.1⟩, hc.2.2.2⟩

/-- The selected-record event. -/
def event (i : D.ι) : Set (S.Ω × HistorySpace 0 0) :=
  {p | (stopRec (rationalTime S.s) p.2,
    stopRec (rationalTime (D.q i)) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) ∈ D.selected i}

/-- The contact: MARKS' contact rule of R1's obstacle, minus the restart time. -/
def contact (i : D.ι) (p : S.Ω × HistorySpace 0 0) : ℝ≥0∞ :=
  contactRule (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (rationalTime (D.q i))
    (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) - rationalTime (D.q i)

/-- **The restart family of the choices.** -/
def src (h : D.HasChart) : SourceRestartData S.Ω S.nL S.nR where
  ι := D.ι
  countable := D.countable
  start := fun i => rationalTime (D.q i)
  selected := D.selected
  chart := D.chart h
  event := D.event
  path := fun i => recordPath S (rationalTime (D.q i))
  contact := D.contact
  data := D.data
  left := D.left
  right := D.right

end R1Restart

section Inputs

variable {S : SourceSetting.{u}} (D : R1Restart S) (h : D.HasChart)

/-- **The genuinely open inputs for the built family** (owner PROVE-AUX61-GLUEINST): measurable selection, R1's chart
data read correctly on the selected records with nonnegative restart times, the restart tip off R1's obstacle, the
window data, and the restart/stop/geometry/comparison/capture facts. -/
structure R1RestartInputs : Prop where
  selected_measurable : ∀ i, MeasurableSet (D.selected i)
  record_Y : ∀ i, ∀ y ∈ D.selected i, D.Y i y = y.1
  record_η : ∀ i, ∀ y ∈ D.selected i, D.η i y = fun t : ℝ => histTrace 0 y.2 t.toNNReal
  q_nonneg : ∀ i, 0 ≤ D.q i
  start_off : ∀ i, ∀ᵐ p ∂S.μ, p ∈ D.event i →
    recordPath S (rationalTime (D.q i)) p 0 ∉ retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
      (sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  open_window : ∀ i, IsOpen (D.data i).V
  zero_window : ∀ i, (0 : ℂ) ∈ (D.data i).V
  clearance : ∀ i, (D.data i).ℓ = clr (D.data i).V
  kappa : ∀ i, (D.data i).κ = S.κ
  reference : ∀ i, Aux61Cov.RefWin (D.data i).κ (D.data i).bR (D.data i).JR (Ioo (D.left i) (D.right i))
  physical_stop : ∀ i, ∀ᵐ p ∂S.μ, sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      D.selected i →
    p ∈ (D.src h).event i ∧ 0 < (D.src h).contact i p ∧
      ((D.src h).contact i p < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < (D.src h).contact i p ∧
      inPath ((D.src h).event i)
        (sourceChart (withRecordPath S (D.src h)) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S (D.src h)).path i) ((D.src h).contact i) p v ∉ (D.data i).V)
  geometric : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (D.src h).event i → RestartGeoRest S (withRecordPath S (D.src h)) i p
  chart_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ (D.src h).event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (rationalTime (D.q i))
      (sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  comparisons : ∀ i, Nonempty (Aux61GAlign.ZeroComparisons (S.marksData (cutSource S (withRecordPath S (D.src h)))) i)
  history_cover : ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i,
    sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ D.selected i
  completed_window : ∀ i, ∀ᵐ p ∂S.μ,
    sourceRecord (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ D.selected i →
    S.windowEvent p → (D.src h).contact i p < ⊤ ∧
    (∀ v : ℝ≥0, (v : ℝ≥0∞) < (D.src h).contact i p →
      inPath ((D.src h).event i) (sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S (D.src h)).path i) ((D.src h).contact i) p v ∈ (D.data i).V) ∧
    ∃ y ∈ Ioo (D.left i) (D.right i),
      Tendsto (inPath ((D.src h).event i)
        (sourceChart (D.src h) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S (D.src h)).path i) ((D.src h).contact i) p)
        (𝓝[<] ((D.src h).contact i p).toNNReal) (𝓝 (y : ℂ))

variable {D h}

/-- The contact of the built family is measurable. -/
theorem R1Restart.measurable_contact (i : D.ι) : Measurable (D.contact i) := by
  obtain ⟨hY₀, hR₀⟩ := measurable_initialRecords (S := S)
  have hrec := hY₀.prodMk hR₀
  have hc := measurable_contactRule (measurable_infDist_retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR))
    (rationalTime (D.q i))
  have hm := hc.comp hrec
  have hmono : Monotone fun x : ℝ≥0∞ => x - (rationalTime (D.q i) : ℝ≥0∞) := fun _ _ hab => tsub_le_tsub_right hab _
  exact hmono.measurable.comp hm

/-- **`R1Inputs` for the built family**: the chart fields from R1's chart theorem, the event fields from the
selected-record preimage, the contact's measurability and first-hit identification from MARKS' contact rule. -/
theorem R1RestartInputs.r1Inputs (hI : R1RestartInputs D h) :
    R1Inputs S (D.src h) fun _ => retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR) where
  selected_measurable := hI.selected_measurable
  chart_measurable := fun i => (D.chart_spec h i).1
  chart_conformal := fun i y _ => (D.chart_spec h i).2.1 y
  chart_lift := fun i y _ => (D.chart_spec h i).2.2.2 y
  chart_domain := fun i => by
    obtain ⟨b, hb⟩ := (D.chart_spec h i).2.2.1
    refine ⟨b, fun y hy => ?_⟩
    have hq : ((rationalTime (D.q i) : ℝ≥0) : ℝ) = (D.q i : ℝ) :=
      Real.coe_toNNReal _ (by exact_mod_cast hI.q_nonneg i)
    have hK : Aux61Restart.historyHull (rationalTime S.s) (D.Y i) y =
        Aux61Restart.historyHull (rationalTime S.s) (fun p : HistorySpace 0 0 × HistorySpace S.nL S.nR => p.1) y := by
      simp only [Aux61Restart.historyHull, hI.record_Y i y hy]
    change ((D.chart h i y).dom : Set ℂ) = connectedComponentIn (Aux61Restart.retainedDomain
      (Aux61Restart.historyHull (rationalTime S.s) (fun p : HistorySpace 0 0 × HistorySpace S.nL S.nR => p.1) y)
      (fun t : ℝ => histTrace 0 y.2 t.toNNReal) ((rationalTime (D.q i) : ℝ≥0) : ℝ)) (b y)
    rw [hb y, hK, hI.record_η i y hy, hq]
  event_measurable := (eventFacts_of_eq_preimage S (D.src h) hI.selected_measurable fun _ => rfl).1
  contact_measurable := D.measurable_contact
  contact_hit := fun i => by
    filter_upwards [hI.start_off i, ae_recordPath S, ae_continuous_ownTrace S] with p h0 hrp hct he
    have h0' := h0 he
    refine ⟨?_, h0'⟩
    have hv := contactRule_eq_add_hitTime (ρ := recordPath S (rationalTime (D.q i)))
      (C := retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (t₀ := rationalTime (D.q i))
      (Y₀ := fun p : S.Ω × HistorySpace 0 0 => stopRec (rationalTime S.s) p.2)
      (R₀ := fun p => killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (x := p) (hrp _).2.1 hct
      (isClosed_retObs _ _) (retObs_nonempty _ _) h0' fun _ _ _ => rfl
    change contactRule (retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)) (rationalTime (D.q i))
      (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) -
        ((rationalTime (D.q i) : ℝ≥0) : ℝ≥0∞) = _
    rw [hv, ENNReal.add_sub_cancel_left ENNReal.coe_ne_top]
    rfl
  open_window := hI.open_window
  zero_window := hI.zero_window
  clearance := hI.clearance
  kappa := hI.kappa
  reference := hI.reference
  event_version := (eventFacts_of_eq_preimage S (D.src h) hI.selected_measurable fun _ => rfl).2
  physical_stop := hI.physical_stop
  geometric := hI.geometric
  chart_geometry := hI.chart_geometry
  comparisons := hI.comparisons
  history_cover := hI.history_cover
  completed_window := hI.completed_window

end Inputs

/-! ### The fibre cover -/

/-- **Theorem 1.2's fibre leaf at universes `u` and `0` from the restart choices**: R1's chart existence `HasChart` and
the inputs `R1RestartInputs` in every source setting at each universe. -/
theorem dyCover_of_r1Restart_both (D : ∀ S : SourceSetting.{u}, R1Restart S) (h : ∀ S, (D S).HasChart)
    (hI : ∀ S, R1RestartInputs (D S) (h S)) (D₀ : ∀ S : SourceSetting.{0}, R1Restart S)
    (h₀ : ∀ S, (D₀ S).HasChart) (hI₀ : ∀ S, R1RestartInputs (D₀ S) (h₀ S)) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin ∧
      Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_r1_retObs_both (fun S => (D S).src (h S)) (fun S => (hI S).r1Inputs)
    (fun S => (D₀ S).src (h₀ S)) fun S => (hI₀ S).r1Inputs

end InteractingSLE.Sec5.Aux61Asm2
