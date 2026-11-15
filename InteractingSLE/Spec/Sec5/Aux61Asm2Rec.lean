/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksSet

/-!
# The completed rule marks record the code and the live chart set: the record readings asked only on the event

Packet PROVE-AUX61-ASSEMBLE2. PROVE-AUX61-MARKS proved `code_le` (`codeFiltration_le_nullRuleMarks_of_record`) and
`baseSets_marks` (`measurable_markedSet_nullRuleMarks`) for the null completion of the rule marks of SLITW's glued
stop `capacityRule c t₀ r`. Its record-reading hypotheses are asked at every sample (almost surely), and its marked
set is cut down to a set `G` on which the readings hold pointwise. This file states both results with the readings
asked **only on the restart event `E`** (the source's restart objects are defined only there), and for the marked set
in the **live** form `liveSet (liveEv Z B Y r) (chartSet …)` used by the assembly:

* `exitNN_of_notMem`: off the event the window exit is `0`;
* `measurableSet_alive_nullRuleMarks_on`, **`codeFiltration_le_nullRuleMarks_on`**: `code_le` from the chart read
  from the time-`0` record, and, almost surely on `E`, the restarted path read from the record before the contact,
  the contact rule, and the window exit;
* `isMeasChart_nullRuleMarks_of_read`: a chart read from the time-`0` record is measurable for the completed marks;
* **`measurable_liveChartSet_nullRuleMarks`**: the live chart set is hitting-measurable for the completed marks when,
  on `E` (pointwise), the restarted path is the record trace and the chart domain is R1's component of the retained
  domain `ℍ ∖ (K₀ ∪ η̃[0, t₀])` (`K₀` hitting-measurable, `η̃` continuous on `[0, t₀]` and measurable at every time).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Asm2

open Aux61Marks Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData Aux61GInst Aux61Fib
open Aux61SlitW (capacityRule)
open Aux61UnionK (chartHull)
open Aux61ChLoc (liveSet liveEv)

universe u

/-! ### Off the event the window exit is `0` -/

section Exit

variable {X : Type*} {E : Set X} {cc : X → Chart} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ} {x : X}

/-- Off the restart event the window exit time is `0`. -/
theorem exitTime_of_notMem (hx : x ∉ E) : Aux61FibData.exitTime E cc ρ T V x = 0 := by
  classical
  simp only [Aux61FibData.exitTime]
  refine le_antisymm (iSup_le fun a => ?_) bot_le
  split_ifs with hw
  · exact absurd hw.1 hx
  · exact le_rfl

/-- Off the restart event the window exit (as a finite time) is `0`. -/
theorem exitNN_of_notMem (hx : x ∉ E) : exitNN E cc ρ T V x = 0 := by
  simp only [exitNN, exitTime_of_notMem hx, ENNReal.toNNReal_zero]

end Exit

/-! ### `code_le` with the record readings asked on the event -/

section Code

variable {X : Type u} [mX : MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Ta : 𝒴 × HistorySpace nL nR → ℝ≥0∞}
  {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR} {μ : Measure X}
include hs hV hV0 hland hinj

/-- **The aliveness events are in the completed rule marks**, with the record readings asked on the event:
`Aux61Marks.measurableSet_alive_nullRuleMarks` with `hrec` restricted to `E` (the proof only uses the readings at
samples of the event). -/
theorem measurableSet_alive_nullRuleMarks_on (hc : IsMeasChart c) (hTam : Measurable Ta)
    (hTaG : IsGalmarinoRule stopRec Ta) (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom)
    (hh : Measurable h) {r r' : ℝ≥0} (hrr : r' ≤ r)
    (hE : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] E)
    (hrec : ∀ᵐ x ∂μ, x ∈ E → cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) ∧
      Ta (Y₀ x, R₀ x) = (t₀ : ℝ≥0∞) + T x)
    (hexit : ∀ᵐ x ∂μ, x ∈ E → x ∈ exitEv E cc ρ T V) :
    MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ]
      {x | ((r' : ℝ≥0) : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life} := by
  have hY := measurable_accessExitCode hs hV hV0 hland hinj hliftc hh (a := a) (k := k)
  obtain ⟨-, E', hE', hEe⟩ := hE
  have hA : MeasurableSet[ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀]
      {x | AliveRec c t₀ Ta V r' r (Y₀ x, stopAt stopRec (capacityRule c t₀ r (Y₀ x, R₀ x)) (R₀ x))} :=
    (measurable_ruleMarks_of_factor (stop := stopRec) (ρ := capacityRule c t₀ r) (Y₀ := Y₀) (R₀ := R₀)
      measurable_id) (measurableSet_aliveRec hc t₀ hTam V r' r)
  refine measurableSet_nullMarks_of_ae_eq
    (measurableSet_lt measurable_const (FibCode.measurable_life.comp hY)) (hE'.inter hA) ?_
  filter_upwards [hEe, hrec, hexit] with x hxE' hx hexx
  have hxE : (x ∈ E) = (x ∈ E') := hxE'
  have hstop : AliveRec c t₀ Ta V r' r (Y₀ x, stopAt stopRec (capacityRule c t₀ r (Y₀ x, R₀ x)) (R₀ x)) ↔
      AliveRec c t₀ Ta V r' r (Y₀ x, R₀ x) := by
    by_cases htop : capacityRule c t₀ r (Y₀ x, R₀ x) < ⊤
    · simp only [stopAt, htop, ↓reduceIte]
      exact aliveRec_stopRec hTaG htop
    · simp only [stopAt, htop, ↓reduceIte]
  refine propext ⟨fun halive => ⟨?_, ?_⟩, fun hJ => ?_⟩
  · have hxe := mem_exitEv_of_lt_accessLife halive
    exact hxE ▸ hxe.1.1
  · have hxe : x ∈ E := (mem_exitEv_of_lt_accessLife halive).1.1
    obtain ⟨hch, hρx, hTax⟩ := hx hxe
    exact hstop.2 (aliveRec_of_alive hs hV hV0 hland hinj hch hρx hTax halive hrr)
  · have hxe : x ∈ E := hxE ▸ hJ.1
    obtain ⟨hch, hρx, hTax⟩ := hx hxe
    exact alive_of_aliveRec hs hV hV0 hland hinj hch hρx hTax (hexx hxe) (hstop.1 hJ.2)

/-- **`code_le` for the completed rule marks, record readings asked on the event**: the raw code σ-algebra at `r` is
in the null completion of the rule marks of the glued stop `capacityRule c t₀ r` when the chart is read from the
time-`0` record (almost surely), and almost surely on `E` the restarted path is the record trace before the contact,
the absolute contact time is the measurable Galmarino rule `Ta`, and the window is exited. -/
theorem codeFiltration_le_nullRuleMarks_on (hc : IsMeasChart c) (hTam : Measurable Ta)
    (hTaG : IsGalmarinoRule stopRec Ta) (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom)
    (hh : Measurable h) (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) (r : ℝ≥0)
    (hE : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] E)
    (hchart : ∀ᵐ x ∂μ, cc x = c (Y₀ x, stopRec t₀ (R₀ x)))
    (hρ : ∀ᵐ x ∂μ, x ∈ E → ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u))
    (hTa : ∀ᵐ x ∂μ, x ∈ E → Ta (Y₀ x, R₀ x) = (t₀ : ℝ≥0∞) + T x)
    (hexit : ∀ᵐ x ∂μ, x ∈ E → x ∈ exitEv E cc ρ T V) :
    (Aux61FibK.codeFiltration.{u} r).comap (fun x => ULift.up.{u} (accessExitCode E cc ρ T V a k h x)) ≤
      nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ := by
  have hrec' : ∀ᵐ x ∂μ, cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u) := by
    filter_upwards [hchart, hρ] with x hcx hρx
    refine ⟨hcx, fun u hu hue => ?_⟩
    by_cases hxE : x ∈ E
    · exact hρx hxE u hu (lt_T_of_lt_exitNN hue)
    · rw [exitNN_of_notMem hxE] at hue
      exact absurd hue (not_lt.2 zero_le)
  have hrec : ∀ᵐ x ∂μ, x ∈ E → cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) ∧
      Ta (Y₀ x, R₀ x) = (t₀ : ℝ≥0∞) + T x := by
    filter_upwards [hchart, hρ, hTa] with x hcx hρx hTx hxE
    exact ⟨hcx, hρx hxE, hTx hxE⟩
  exact codeFiltration_le_nullRuleMarks hs hV hV0 hland hinj hc d hdV hℓ hliftc hh r hrec'
    fun r' hr' => measurableSet_alive_nullRuleMarks_on hs hV hV0 hland hinj hc hTam hTaG hliftc hh hr' hE hrec hexit

end Code

/-! ### Charts read from the time-`0` record -/

section Chart

variable {X : Type*} [mX : MeasurableSpace X] {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {ρr : 𝒴 × HistorySpace nL nR → ℝ≥0∞}
  {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR} {μ : Measure X}

/-- **A chart read from the time-`0` record is a measurable chart for the completed rule marks** (rules after
`t₀`). -/
theorem isMeasChart_nullRuleMarks_of_read (hc : IsMeasChart c) (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ ρr p)
    (hρm : Measurable ρr) (hY₀ : Measurable Y₀) (hR₀ : Measurable R₀) :
    @IsMeasChart X (nullMarks (ruleMarks stopRec ρr Y₀ R₀) μ) fun x => c (Y₀ x, stopRec t₀ (R₀ x)) := by
  have h0 := isMeasChart_ruleMarks_of_time0 (X := X) (Y₀ := Y₀) (R₀ := R₀) hc isRecordStop_stopRec hle
  have hsm : ruleMarks stopRec ρr Y₀ R₀ ≤ nullMarks (ruleMarks stopRec ρr Y₀ R₀) μ :=
    le_nullMarks (ruleMarks_le isRecordStop_stopRec hρm hY₀ hR₀)
  exact @IsMeasChart.mk X (nullMarks (ruleMarks stopRec ρr Y₀ R₀) μ) _
    (fun z => hsm _ (@IsMeasChart.dom X (ruleMarks stopRec ρr Y₀ R₀) _ h0 z))
    (fun z => (@IsMeasChart.fwd X (ruleMarks stopRec ρr Y₀ R₀) _ h0 z).mono hsm le_rfl)
    (fun z => (@IsMeasChart.lift X (ruleMarks stopRec ρr Y₀ R₀) _ h0 z).mono hsm le_rfl)

end Chart

/-! ### The live chart set is recorded by the completed marks -/

section Sets

variable {X : Type u} [mX : MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Ta : 𝒴 × HistorySpace nL nR → ℝ≥0∞}
  {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR} {μ : Measure X}
include hs hV hV0 hland hinj

/-- **`baseSets_marks` for the live chart set**: on the live event `{Z ∈ B, r < life}` the chart set
`chartSet c K_r` of the access code, `ℍ` off it, is hitting-measurable for the null completion of the rule marks of
the glued stop `capacityRule c t₀ r`, when the chart is read from the time-`0` record, the history event and the
restart event are completed-mark events, and **on the restart event** (pointwise) the restarted path is the record
trace before the contact and the chart domain is R1's component of the retained domain `ℍ ∖ (K₀ ∪ η[0, t₀])` with a
hitting-measurable obstacle `K₀` and a prefix `η` continuous on `[0, t₀]` and measurable at every time; almost surely
on the restart event the absolute contact time is the Galmarino rule `Ta` and the window is exited. -/
theorem measurable_liveChartSet_nullRuleMarks (hc : IsMeasChart c) (hTam : Measurable Ta)
    (hTaG : IsGalmarinoRule stopRec Ta) (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom)
    (hh : Measurable h) (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) (hY₀ : Measurable Y₀)
    (hR₀ : Measurable R₀) (r : ℝ≥0) {β : Type*} {Z : X → β} {B : Set β}
    (hZB : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] (Z ⁻¹' B))
    (hE : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] E)
    (hchart : ∀ x, cc x = c (Y₀ x, stopRec t₀ (R₀ x)))
    (hρ : ∀ x ∈ E, ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u))
    (hTa : ∀ᵐ x ∂μ, x ∈ E → Ta (Y₀ x, R₀ x) = (t₀ : ℝ≥0∞) + T x)
    (hexit : ∀ᵐ x ∂μ, x ∈ E → x ∈ exitEv E cc ρ T V) {K₀ : X → Set ℂ}
    (hK₀ : Measurable[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ, hittingSigma] K₀)
    {η : X → ℝ → ℂ} (hηc : ∀ x ∈ E, ContinuousOn (η x) (Icc 0 (t₀ : ℝ)))
    (hηm : ∀ v : ℝ, Measurable[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] fun x => η x v)
    {b : X → ℂ} (hdom : ∀ x ∈ E, ((cc x).dom : Set ℂ) =
      connectedComponentIn (Aux61Restart.retainedDomain (K₀ x) (η x) t₀) (b x)) :
    Measurable[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ, hittingSigma]
      (liveSet (liveEv Z B (accessExitCode E cc ρ T V a k h) r)
        fun x => chartSet (cc x) (chartHull (accessExitCode E cc ρ T V a k h) r x)) := by
  have hrec : ∀ᵐ x ∂μ, x ∈ E → cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) ∧
      Ta (Y₀ x, R₀ x) = (t₀ : ℝ≥0∞) + T x := by
    filter_upwards [hTa] with x hTx hxE
    exact ⟨hchart x, hρ x hxE, hTx hxE⟩
  have halive := measurableSet_alive_nullRuleMarks_on hs hV hV0 hland hinj (a := a) (k := k) hc hTam hTaG hliftc hh
    (le_refl r) hE hrec hexit
  have hGm : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ]
      (liveEv Z B (accessExitCode E cc ρ T V a k h) r) := hZB.inter halive
  have hcc : cc = fun x => c (Y₀ x, stopRec t₀ (R₀ x)) := funext hchart
  have hcm : @IsMeasChart X (nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ) cc := by
    rw [hcc]
    exact isMeasChart_nullRuleMarks_of_read hc (Aux61SlitW.start_le_capacityRule c t₀ r)
      (Aux61SlitW.measurable_capacityRule hc t₀ r) hY₀ hR₀
  have hEof : ∀ x ∈ liveEv Z B (accessExitCode E cc ρ T V a k h) r, x ∈ E := fun x hx =>
    (mem_exitEv_of_lt_accessLife hx.2).1.1
  exact measurable_markedSet_nullRuleMarks hs hV hV0 hland hinj d hdV hℓ hc hY₀ hR₀ hGm
    (R := fun x => Aux61Restart.retainedDomain (K₀ x) (η x) t₀) (b := b)
    (fun x hx => ⟨hx.2, hchart x, fun u hu hue => hρ x (hEof x hx) u hu (lt_T_of_lt_exitNN hue),
      hdom x (hEof x hx)⟩) hcm
    (fun p => exists_retained_event hK₀ t₀.2 (fun x hx => hηc x (hEof x hx)) hηm p)

end Sets

end InteractingSLE.Sec5.Aux61Asm2
