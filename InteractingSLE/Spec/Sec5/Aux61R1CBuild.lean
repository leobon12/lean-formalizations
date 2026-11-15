/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61R1CChart
import InteractingSLE.Spec.Sec5.Aux61R1CInputs

/-!
# The R1 restart data built from the restart choices: `HasChart` and the selection facts proved

Packet PROVE-AUX61-R1CHART. `RestartChoices S` are PROVE-AUX61-GLUEINST's choices (countable index, rational restart
times, selected initial records, window data). `RestartChoices.toR1Restart` is ASSEMBLE2's `R1Restart S`:

* the index is restricted to the indices having a good record (`goodSet`, `Aux61R1CChart`), the selection is
  intersected with the good records (an index without good records selects nothing anyway);
* R1's chart data are read through the measurable retraction onto the good records (`finY`, `finU`, `finη`), with
  the dense base sequence `baseSeq`.

Proved here, for every choice: **`hasChart`** (R1's chart at every record, every index), **`selected_measurable`**
(from the choices' measurability), **`record_Y`**, **`record_η`** (the plain record readers on the selected records;
the trace on `[0, q]`), **`q_nonneg`** and **`start_off`** (the restart tip is off the counterflow hull and `ℝ`).
`ChoiceInputs` lists the remaining GLUEINST inputs (window data, physical stop, geometry, comparisons, capture), with
the history cover stated on the original index; `ChoiceInputs.r1RestartInputsC` and `dyCover_of_choices_both` give the
dyadic fibre cover at universes `u` and `0`.
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

/-- **The restart choices** (owner PROVE-AUX61-GLUEINST): countable index, rational restart times, selected initial
records, window data. -/
structure RestartChoices (S : SourceSetting.{u}) where
  ι : Type
  [countable : Countable ι]
  q : ι → ℚ
  selected : ι → Set (SourceRecord S.nL S.nR)
  data : ι → FibData
  left : ι → ℝ
  right : ι → ℝ

attribute [instance] RestartChoices.countable

/-- The counterflow time of a source setting is positive. -/
theorem rationalTime_s_pos (S : SourceSetting.{u}) : 0 < rationalTime S.s :=
  Real.toNNReal_pos.2 (by exact_mod_cast S.s_pos)

namespace RestartChoices

variable {S : SourceSetting.{u}} (C : RestartChoices S)

/-- The good records of an index. -/
abbrev good (i : C.ι) : Set (SourceRecord S.nL S.nR) := goodSet (rationalTime S.s) (C.q i)

/-- The initial records of an index. -/
def record (i : C.ι) (p : S.Ω × HistorySpace 0 0) : SourceRecord S.nL S.nR :=
  (stopRec (rationalTime S.s) p.2,
    stopRec (rationalTime (C.q i)) (killedHistory S.own.W S.own.VL S.own.VR S.life p.1))

/-- The indices with a good record. -/
abbrev Idx : Type := {i : C.ι // (C.good i).Nonempty}

/-- **The R1 restart data of the choices.** -/
def toR1Restart : R1Restart S where
  ι := C.Idx
  countable := inferInstance
  q := fun i => C.q i.1
  selected := fun i => C.selected i.1 ∩ C.good i.1
  data := fun i => C.data i.1
  left := fun i => C.left i.1
  right := fun i => C.right i.1
  r := fun i => rationalTime (C.q i.1)
  U := fun i => finU (rationalTime S.s) (C.q i.1)
  e := baseSeq
  Y := fun i => finY (rationalTime S.s) (C.q i.1)
  η := fun i => finη (rationalTime S.s) (C.q i.1)

/-- **R1's chart existence for the built data** (`HasChart`). -/
theorem hasChart : C.toR1Restart.HasChart := fun i => Aux61R1C.hasChart (rationalTime_s_pos S) i.2

/-- The built restart family. -/
abbrev fam : SourceRestartData S.Ω S.nL S.nR := C.toR1Restart.src C.hasChart

theorem selected_measurable (hsel : ∀ i, MeasurableSet (C.selected i)) :
    ∀ i, MeasurableSet (C.toR1Restart.selected i) := fun i =>
  (hsel i.1).inter (measurableSet_goodSet _ _)

theorem record_Y : ∀ i, ∀ y ∈ C.toR1Restart.selected i, C.toR1Restart.Y i y = y.1 := fun _ _ hy =>
  finY_of_mem hy.2

theorem record_η : ∀ i, ∀ y ∈ C.toR1Restart.selected i,
    EqOn (C.toR1Restart.η i y) (fun t : ℝ => histTrace 0 y.2 t.toNNReal) (Icc 0 (C.toR1Restart.q i : ℝ)) :=
  fun _ _ hy => finη_eqOn hy.2

theorem q_nonneg : ∀ i, 0 ≤ C.toR1Restart.q i := fun i => by
  obtain ⟨y, hy⟩ := i.2
  exact hy.1.1.le

/-- The restart tip read from the own record is the record trace at the restart time. -/
theorem recordPath_zero_eq (t₀ : ℝ≥0) (p : S.Ω × HistorySpace 0 0) :
    recordPath S t₀ p 0 = histTrace 0 (stopRec t₀ (killedHistory S.own.W S.own.VL S.own.VR S.life p.1)) t₀ := by
  rw [histTrace_stopRec_of_le le_rfl]
  unfold recordPath
  rw [add_zero]

/-- **The restart tip lies off the counterflow hull and `ℝ`** (at every sample of the event). -/
theorem start_off : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.toR1Restart.event i →
    recordPath S (rationalTime (C.toR1Restart.q i)) p 0 ∉ retObs (rationalTime S.s) (β := HistorySpace S.nL S.nR)
      (sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p) := by
  intro i
  refine Eventually.of_forall fun p hp => ?_
  have hgood : C.record i.1 p ∈ C.good i.1 := hp.2
  rw [recordPath_zero_eq]
  exact recTrace_notMem_retObs hgood.2.1

end RestartChoices

/-- **The remaining inputs of the built family** (owner PROVE-AUX61-GLUEINST): the choices' measurability and window
data on the original index, the physical stop, geometry, comparisons and capture of the built family, and the history
cover by good selected records. -/
structure RestartChoices.ChoiceInputs {S : SourceSetting.{u}} (C : RestartChoices S) : Prop where
  selected_measurable : ∀ i, MeasurableSet (C.selected i)
  open_window : ∀ i, IsOpen (C.data i).V
  zero_window : ∀ i, (0 : ℂ) ∈ (C.data i).V
  clearance : ∀ i, (C.data i).ℓ = clr (C.data i).V
  kappa : ∀ i, (C.data i).κ = S.κ
  reference : ∀ i, Aux61Cov.RefWin (C.data i).κ (C.data i).bR (C.data i).JR (Ioo (C.left i) (C.right i))
  physical_stop : ∀ i, ∀ᵐ p ∂S.μ, sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈
      C.toR1Restart.selected i →
    p ∈ C.fam.event i ∧ 0 < C.fam.contact i p ∧
      (C.fam.contact i p < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < C.fam.contact i p ∧
      inPath (C.fam.event i)
        (sourceChart (withRecordPath S C.fam) (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S C.fam).path i) (C.fam.contact i) p v ∉ (C.toR1Restart.data i).V)
  geometric : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i → RestartGeoRest S (withRecordPath S C.fam) i p
  chart_geometry : ∀ i, ∀ᵐ p ∂S.μ, p ∈ C.fam.event i →
    SourceChartGeometry (fun t : ℝ => S.own.W t.toNNReal p.1) (fun t => S.path p.1 t.toNNReal)
      (cfHullQ (rationalTime S.s) p.2) (rationalTime (C.toR1Restart.q i))
      (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p)
  comparisons : ∀ i, Nonempty (Aux61GAlign.ZeroComparisons (S.marksData (cutSource S (withRecordPath S C.fam))) i)
  history_cover : ∀ᵐ p ∂S.μ, S.windowEvent p → ∃ i, C.record i p ∈ C.selected i ∧ C.record i p ∈ C.good i
  completed_window : ∀ i, ∀ᵐ p ∂S.μ,
    sourceRecord C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i p ∈ C.toR1Restart.selected i →
    S.windowEvent p → C.fam.contact i p < ⊤ ∧
    (∀ v : ℝ≥0, (v : ℝ≥0∞) < C.fam.contact i p →
      inPath (C.fam.event i) (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S C.fam).path i) (C.fam.contact i) p v ∈ (C.toR1Restart.data i).V) ∧
    ∃ y ∈ Ioo (C.toR1Restart.left i) (C.toR1Restart.right i),
      Tendsto (inPath (C.fam.event i)
        (sourceChart C.fam (rationalTime S.s) S.own.W S.own.VL S.own.VR S.life i)
        ((withRecordPath S C.fam).path i) (C.fam.contact i) p)
        (𝓝[<] (C.fam.contact i p).toNNReal) (𝓝 (y : ℂ))

/-- **All inputs of the built family**: R1CHART's fields proved, GLUEINST's from `ChoiceInputs`. -/
theorem RestartChoices.ChoiceInputs.r1RestartInputsC {S : SourceSetting.{u}} {C : RestartChoices S}
    (hC : C.ChoiceInputs) : R1RestartInputsC C.toR1Restart C.hasChart where
  selected_measurable := C.selected_measurable hC.selected_measurable
  record_Y := C.record_Y
  record_η := C.record_η
  q_nonneg := C.q_nonneg
  start_off := C.start_off
  open_window := fun i => hC.open_window i.1
  zero_window := fun i => hC.zero_window i.1
  clearance := fun i => hC.clearance i.1
  kappa := fun i => hC.kappa i.1
  reference := fun i => hC.reference i.1
  physical_stop := hC.physical_stop
  geometric := hC.geometric
  chart_geometry := hC.chart_geometry
  comparisons := hC.comparisons
  history_cover := by
    filter_upwards [hC.history_cover] with p hp hw
    obtain ⟨i, hsel, hgood⟩ := hp hw
    exact ⟨⟨i, _, hgood⟩, hsel, hgood⟩
  completed_window := hC.completed_window

/-- **Theorem 1.2's fibre leaf at universes `u` and `0` from GLUEINST's restart choices and their inputs.** -/
theorem dyCover_of_choices_both (C : ∀ S : SourceSetting.{u}, RestartChoices S) (hC : ∀ S, (C S).ChoiceInputs)
    (C₀ : ∀ S : SourceSetting.{0}, RestartChoices S) (hC₀ : ∀ S, (C₀ S).ChoiceInputs) :
    Aux61Act.DyActFibreCoverOn.{u} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin ∧
      Aux61Act.DyActFibreCoverOn.{0} (fun κ θ₁ θ₂ => ¬ Prop51G.IsLargeGap κ θ₁ θ₂) Aux61Cov.RefWin :=
  dyCover_of_r1RestartC_both (fun S => (C S).toR1Restart) (fun S => (C S).hasChart)
    (fun S => (hC S).r1RestartInputsC) (fun S => (C₀ S).toR1Restart) (fun S => (C₀ S).hasChart)
    fun S => (hC₀ S).r1RestartInputsC

end InteractingSLE.Sec5.Aux61R1C
