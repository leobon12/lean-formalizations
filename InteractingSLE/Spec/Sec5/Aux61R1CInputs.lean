/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61Asm2Build

/-!
# The restart family's inputs with R1's trace read on `[0, q]` only

Packet PROVE-AUX61-R1CHART. ASSEMBLE2's `R1RestartInputs` asks, on the selected records, `η i y` to be the record
reader `t ↦ histTrace 0 y.2 t` at **every** time. Together with `HasChart` this cannot hold: R1's chart theorem needs
`η i y` to be a continuous Loewner trace on `[0, ∞)`, while after the restart time `q` the record (stopped at `q`) reads
the trace of the driver killed to `0` there, which jumps at `q` (unless the driver vanishes at `q`). Only the values on
`[0, q]` are used — the retained domain removes `η '' [0, q]` — so `R1RestartInputsC` asks the identity on `[0, q]`
(`record_η`); everything else is ASSEMBLE2's `R1RestartInputs` unchanged. `R1RestartInputsC.r1Inputs` is ASSEMBLE2's
proof of `R1Inputs` with this change, and `dyCover_of_r1RestartC_both` the cover.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61R1C

open Aux61Asm2 Aux61Marks Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData Aux61GInst Aux61Fib
open Aux61SlitW (SourceRestartData SourceRestartFacts SourceRecord SourceSetting SourceChartGeometry sourceChart
  sourceRecord rationalTime)
open GlueCond (cfHullQ)

universe u

section Inputs

variable {S : SourceSetting.{u}} (D : R1Restart S) (h : D.HasChart)

/-- **ASSEMBLE2's inputs for the built family, with R1's trace read on `[0, q]` only** (`record_η`). -/
structure R1RestartInputsC : Prop where
  selected_measurable : ∀ i, MeasurableSet (D.selected i)
  record_Y : ∀ i, ∀ y ∈ D.selected i, D.Y i y = y.1
  record_η : ∀ i, ∀ y ∈ D.selected i,
    EqOn (D.η i y) (fun t : ℝ => histTrace 0 y.2 t.toNNReal) (Icc 0 (D.q i : ℝ))
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

/-- **`R1Inputs` for the built family** (ASSEMBLE2's `R1RestartInputs.r1Inputs`, with R1's trace identified with the
record reader on `[0, q]` only — all the retained domain uses). -/
theorem R1RestartInputsC.r1Inputs (hI : R1RestartInputsC D h) :
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
    have hR : Aux61Restart.retainedDomain (Aux61Restart.historyHull (rationalTime S.s) (D.Y i) y) (D.η i y)
        (D.q i) = Aux61Restart.retainedDomain
          (Aux61Restart.historyHull (rationalTime S.s) (fun p : HistorySpace 0 0 × HistorySpace S.nL S.nR => p.1) y)
          (fun t : ℝ => histTrace 0 y.2 t.toNNReal) ((rationalTime (D.q i) : ℝ≥0) : ℝ) := by
      rw [hK, hq]
      unfold Aux61Restart.retainedDomain
      rw [(hI.record_η i y hy).image_eq]
    change ((D.chart h i y).dom : Set ℂ) = connectedComponentIn (Aux61Restart.retainedDomain
      (Aux61Restart.historyHull (rationalTime S.s) (fun p : HistorySpace 0 0 × HistorySpace S.nL S.nR => p.1) y)
      (fun t : ℝ => histTrace 0 y.2 t.toNNReal) ((rationalTime (D.q i) : ℝ≥0) : ℝ)) (b y)
    rw [hb y, hR]
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

/-- **Theorem 1.2's fibre leaf at universes `u` and `0` from the restart choices**, with R1's trace read on `[0, q]`
(`R1RestartInputsC`). -/
theorem dyCover_of_r1RestartC_both (D : ∀ S : SourceSetting.{u}, R1Restart S) (h : ∀ S, (D S).HasChart)
    (hI : ∀ S, R1RestartInputsC (D S) (h S)) (D₀ : ∀ S : SourceSetting.{0}, R1Restart S)
    (h₀ : ∀ S, (D₀ S).HasChart) (hI₀ : ∀ S, R1RestartInputsC (D₀ S) (h₀ S)) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin ∧
      Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_r1_retObs_both (fun S => (D S).src (h S)) (fun S => (hI S).r1Inputs)
    (fun S => (D₀ S).src (h₀ S)) fun S => (hI₀ S).r1Inputs

end InteractingSLE.Sec5.Aux61R1C
