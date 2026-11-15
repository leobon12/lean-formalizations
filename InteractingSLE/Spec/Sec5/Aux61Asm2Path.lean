/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Asm2Inputs

/-!
# The canonical restart path: the own flow's record trace after the start

Packet PROVE-AUX61-ASSEMBLE2. The restart path of the source is the continuation `η(t₀ + ·)` of the given flow line.
Its version read from the own killed history, `recordPath S t₀ p v = histTrace 0 (killedHistory W V ζ p.1) (t₀ + v)`,
is measurable at every time, and almost surely equals the physical continuation, is continuous and injective (the
flow line is a proper arc). `withRecordPath S F` replaces the path of a restart family by it.

`RecordInputs S F Ta` is `RawInputs` for `withRecordPath S F` without the path inputs: no `path_version`, no path
measurability, and the per-sample restart clauses only for the chart (`RestartGeoPt`: conformality, start, inside,
landing, R1's lift). **`RecordInputs.rawInputs`** proves `RawInputs`, hence (`dyCover_of_record`,
`dyCover_of_record_both`) the dyadic fibre cover at universes `u` and `0`.
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
  sourceRecord rationalTime)
open Aux61ChLoc (IsChartGaussAt)
open GlueCond (cfHullQ)

universe u

section RecordPath

variable (S : SourceSetting.{u})

/-- **The own flow's record trace after the start `t₀`.** -/
def recordPath (t₀ : ℝ≥0) (p : S.Ω × HistorySpace 0 0) (v : ℝ≥0) : ℂ :=
  histTrace 0 (killedHistory S.own.W S.own.VL S.own.VR S.life p.1) (t₀ + v)

theorem measurable_recordPath (t₀ v : ℝ≥0) : Measurable fun p => recordPath S t₀ p v :=
  (measurable_histTrace 0 (t₀ + v)).comp ((measurable_killedHistory S.own.coupling.2.2.2.1).comp measurable_fst)

/-- **Almost surely the record path is the physical continuation, continuous and injective.** -/
theorem ae_recordPath : ∀ᵐ p ∂S.μ, ∀ t₀ : ℝ≥0,
    (∀ v, recordPath S t₀ p v = S.path p.1 (t₀ + v)) ∧ Continuous (recordPath S t₀ p) ∧
      Function.Injective (recordPath S t₀ p) := by
  have htr := ae_histTrace_killedHistory S.own.coupling.1 S.own.trace
    (WangWu.glueMeasure_fst S.kernel S.measCounterField)
  filter_upwards [htr, S.physical_path] with p ht hg t₀
  have he : ∀ v, recordPath S t₀ p v = S.path p.1 (t₀ + v) := fun v =>
    ht (t₀ + v) (by rw [hg.1.1]; exact ENNReal.coe_lt_top)
  have hreal : ∀ t : ℝ≥0, S.path p.1 t = (fun t : ℝ => S.path p.1 t.toNNReal) (t : ℝ) := fun t => by
    simp only [Real.toNNReal_coe]
  have hcont : Continuous (S.path p.1) := by
    have h := hg.2.1.2.1.comp_continuous NNReal.continuous_coe fun t => (t.2 : (0 : ℝ) ≤ t)
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, Real.toNNReal_coe]
  refine ⟨he, ?_, fun u v huv => ?_⟩
  · rw [show recordPath S t₀ p = fun v => S.path p.1 (t₀ + v) from funext he]
    exact hcont.comp (continuous_const.add continuous_id)
  · rw [he, he, hreal, hreal] at huv
    have h := hg.2.2.inj (NNReal.coe_nonneg (t₀ + u)) (NNReal.coe_nonneg (t₀ + v)) huv
    exact add_left_cancel (NNReal.coe_injective h)

/-- **The restart family with the canonical restart path.** -/
def withRecordPath (F : SourceRestartData S.Ω S.nL S.nR) : SourceRestartData S.Ω S.nL S.nR where
  ι := F.ι
  countable := F.countable
  start := F.start
  selected := F.selected
  chart := F.chart
  event := F.event
  path := fun i => recordPath S (F.start i)
  contact := F.contact
  data := F.data
  left := F.left
  right := F.right

variable (F : SourceRestartData S.Ω S.nL S.nR)

/-- **The per-sample restart clauses that concern the chart** (`RestartPt` without the continuity and injectivity of
the path). -/
def RestartGeoPt (i : F.ι) (p : S.Ω × HistorySpace 0 0) : Prop :=
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
  ContinuousOn (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.2
    (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom ∧
  InnerProductSpace.HarmonicOnNhd (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).2.2
    (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom

/-- **The restart/window facts for the canonical path** (owner PROVE-AUX61-GLUEINST): `RawRestartFacts` for
`withRecordPath S F` without the path's measurability, continuity and injectivity. -/
structure RecordRestartFacts : Prop where
  selected_measurable : ∀ i, MeasurableSet (F.selected i)
  chart_measurable : ∀ i, IsMeasChart (F.chart i)
  event_measurable : ∀ i, MeasurableSet (F.event i)
  contact_measurable : ∀ i, Measurable (F.contact i)
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
  geometric : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → RestartGeoPt S (withRecordPath S F) i p

/-- The raw restart facts of the family with the canonical path. -/
theorem RecordRestartFacts.raw {F : SourceRestartData S.Ω S.nL S.nR} (hR : RecordRestartFacts S F) :
    RawRestartFacts S (withRecordPath S F) where
  selected_measurable := hR.selected_measurable
  chart_measurable := hR.chart_measurable
  event_measurable := hR.event_measurable
  contact_measurable := hR.contact_measurable
  path_measurable := fun i u => measurable_recordPath S (F.start i) u
  open_window := hR.open_window
  zero_window := hR.zero_window
  clearance := hR.clearance
  kappa := hR.kappa
  reference := hR.reference
  event_version := hR.event_version
  physical_stop := hR.physical_stop
  regular := fun i => by
    filter_upwards [hR.geometric i, ae_recordPath S] with p hp hrp he
    obtain ⟨hconf, hmem, hlim, hin, hland, hlc, hlh⟩ := hp he
    exact ⟨(hrp (F.start i)).2.1, hconf, hmem, hlim, hin, hland, (hrp (F.start i)).2.2.injOn, hlc, hlh⟩

/-- The canonical restart path is almost surely the physical continuation. -/
theorem path_version_withRecordPath (i : F.ι) : ∀ᵐ p ∂S.μ, p ∈ (withRecordPath S F).event i →
    ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < (withRecordPath S F).contact i p →
      (withRecordPath S F).path i p v = S.path p.1 ((withRecordPath S F).start i + v) := by
  filter_upwards [ae_recordPath S] with p hrp _ v _ _
  exact (hrp (F.start i)).1 v

end RecordPath

/-! ### The inputs for the canonical path -/

section Inputs

variable (S : SourceSetting.{u}) (F : SourceRestartData S.Ω S.nL S.nR)
  (Ta : F.ι → SourceRecord S.nL S.nR → ℝ≥0∞)

/-- **The still-open physical inputs with the canonical restart path** (owner PROVE-AUX61-GLUEINST): `RawInputs` for
`withRecordPath S F` without `path_version`, with `RecordRestartFacts`. -/
structure RecordInputs : Prop where
  restart : RecordRestartFacts S F
  contact_measurable : ∀ i, Measurable (Ta i)
  contact_galmarino : ∀ i, IsGalmarinoRule stopRec (Ta i)
  contact_rule : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    Ta i (stopRec (rationalTime S.s) p.2, killedHistory S.own.W S.own.VL S.own.VR S.life p.1) =
      (F.start i : ℝ≥0∞) + F.contact i p
  dom_component : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i → ∃ b : ℂ,
    ((sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p).dom : Set ℂ) =
      connectedComponentIn (Aux61Restart.retainedDomain (cfHullQ (rationalTime S.s) p.2)
        (fun t : ℝ => S.path p.1 t.toNNReal) (F.start i)) b
  chart_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ F.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (F.start i)
      (sourceChart F (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  initial_data : ∀ i, ∃ g : S.Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens,
    IsChartGaussAt S.μ ((S.marksData (cutSource S (withRecordPath S F))).Z i)
      ((S.marksData (cutSource S (withRecordPath S F))).B i)
      ((S.marksData (cutSource S (withRecordPath S F))).code i) 0
      ((S.marksData (cutSource S (withRecordPath S F))).sigma i 0) g ∧
      Nonempty (Aux61GCont.InitialWindowData (S.Ω × HistorySpace 0 0)
        (S.μ.restrict ((S.marksData (cutSource S (withRecordPath S F))).Z i ⁻¹'
          (S.marksData (cutSource S (withRecordPath S F))).B i)) (F.data i) g)
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

variable {S F Ta}

/-- **`RawInputs` for the family with the canonical path.** -/
theorem RecordInputs.rawInputs (hI : RecordInputs S F Ta) : RawInputs S (withRecordPath S F) Ta where
  restart := hI.restart.raw
  contact_measurable := hI.contact_measurable
  contact_galmarino := hI.contact_galmarino
  contact_rule := hI.contact_rule
  path_version := path_version_withRecordPath S F
  dom_component := hI.dom_component
  chart_geometry := hI.chart_geometry
  initial_data := hI.initial_data
  history_cover := hI.history_cover
  completed_window := hI.completed_window

end Inputs

/-! ### The fibre cover -/

/-- **Theorem 1.2's fibre leaf with the canonical restart paths**: the dyadic fibre cover from restart families
(event, chart, contact, window data) and contact rules in every source setting with the inputs `RecordInputs`. -/
theorem dyCover_of_record (F : ∀ S : SourceSetting.{u}, SourceRestartData S.Ω S.nL S.nR)
    (Ta : ∀ S : SourceSetting.{u}, (F S).ι → SourceRecord S.nL S.nR → ℝ≥0∞)
    (hI : ∀ S : SourceSetting.{u}, RecordInputs S (F S) (Ta S)) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_raw (fun S => withRecordPath S (F S)) Ta fun S => (hI S).rawInputs

/-- **The fibre cover at universes `u` and `0`** with the canonical restart paths. -/
theorem dyCover_of_record_both (F : ∀ S : SourceSetting.{u}, SourceRestartData S.Ω S.nL S.nR)
    (Ta : ∀ S : SourceSetting.{u}, (F S).ι → SourceRecord S.nL S.nR → ℝ≥0∞)
    (hI : ∀ S : SourceSetting.{u}, RecordInputs S (F S) (Ta S))
    (F₀ : ∀ S : SourceSetting.{0}, SourceRestartData S.Ω S.nL S.nR)
    (Ta₀ : ∀ S : SourceSetting.{0}, (F₀ S).ι → SourceRecord S.nL S.nR → ℝ≥0∞)
    (hI₀ : ∀ S : SourceSetting.{0}, RecordInputs S (F₀ S) (Ta₀ S)) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin ∧
      Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  ⟨dyCover_of_record F Ta hI, dyCover_of_record F₀ Ta₀ hI₀⟩

end InteractingSLE.Sec5.Aux61Asm2
