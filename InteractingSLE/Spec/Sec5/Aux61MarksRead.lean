/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksNull
import InteractingSLE.Spec.Restart.FlowStopIdentGRule
import InteractingSLE.Spec.Sec5.Aux61FibDataChart

/-!
# Record measurability: the history, event, chart and code as functions of the rule record

Packet PROVE-AUX61-MARKS. The physical marks at fibre time `r` are the (null-completed) rule marks of the glued stop
`ρ_r` (`Aux61MarksNull`); at time `0` the rule is the restart time `t₀` (SLITW's `capacityRule`: `rule 0 = t₀`,
`rule 0 ≤ rule q`). Here:

* **functions of the record stopped at a time below the rule** are measurable for the rule marks
  (`measurable_ruleMarks_stopAt_le`, `measurable_ruleMarks_of_time0`); in particular the history, the event and the
  chart, read from the time-`0` record `(Y₀, stop t₀ R₀)` (the interface of SLITW's `exists_selectedAccessRule`), are
  recorded by the time-`0` marks (`isMeasChart_ruleMarks_of_time0`), and their almost surely equal versions by the
  completed marks (`isMeasChart_nullMarks_of_ae_eq`);
* the **record readers** of the flow's driving state and trace (`Restart.FlowStopIdentG.histState`, `histTrace`) at
  times `≤ t₀` only read the record stopped at `t₀` (`histState_stopRec_of_le`, `histTrace_stopRec_of_le`), so they are
  measurable for the time-`0` rule marks (`measurable_ruleMarks_histState`, `measurable_ruleMarks_histTrace`), and on a
  space carrying the flow line's coupling they are almost surely the driving state and the generating trace
  (`ae_histState_killedHistory`,
  `ae_histTrace_killedHistory`): the measurable own driver / trace / observation inputs of
  R1's chart (`has_original_target_restart_chart_of_protection`: `hY`, `hUm`, `hm`) for the time-`0` marks;
* **the raw code at `r` in the completed marks** (`codeFiltration_le_nullMarks_of_ae_agree`): it suffices that the
  code agrees almost surely up to `r` (aliveness and driver at every `r' ≤ r`) with a code measurable for the marks.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61ULoc LawUnique Restart.FlowStopIdentG
open Aux61FibData (IsMeasChart)

/-! ### Functions of the time-`0` record -/

section Time0

variable {X 𝒴 γ : Type*} [mX : MeasurableSpace X] [m𝒴 : MeasurableSpace 𝒴] [mγ : MeasurableSpace γ]
  {stop : ℝ≥0 → γ → γ} {ρ : 𝒴 × γ → ℝ≥0∞} {Y₀ : X → 𝒴} {R₀ : X → γ}

omit mX in
/-- **The record stopped at a time below the rule is recorded by the rule marks.** -/
theorem measurable_ruleMarks_stopAt_le (hstop : IsRecordStop stop) {t₀ : ℝ≥0∞} (hle : ∀ p, t₀ ≤ ρ p) :
    Measurable[ruleMarks stop ρ Y₀ R₀] fun x => (Y₀ x, stopAt stop t₀ (R₀ x)) := by
  have e : (fun x => (Y₀ x, stopAt stop t₀ (R₀ x))) =
      (fun q : 𝒴 × γ => (q.1, stopAt stop t₀ q.2)) ∘
        fun x => (Y₀ x, stopAt stop (ρ (Y₀ x, R₀ x)) (R₀ x)) := by
    funext x
    simp only [Function.comp_apply, Aux61Nest.stopAt_stopAt_of_le hstop (hle _)]
  rw [e]
  exact (measurable_fst.prodMk ((measurable_stopAt hstop).comp (measurable_const.prodMk measurable_snd))).comp
    (comap_measurable _)

omit m𝒴 mγ in
/-- Stopping at a finite time is the record stop. -/
theorem stopAt_coe (t₀ : ℝ≥0) (g : γ) : stopAt stop (t₀ : ℝ≥0∞) g = stop t₀ g := by
  simp only [stopAt, ENNReal.coe_lt_top, ↓reduceIte, ENNReal.toNNReal_coe]

omit mX in
/-- **A function of the time-`0` record is recorded by the rule marks** (for a rule at least the restart time). -/
theorem measurable_ruleMarks_of_time0 {δ : Type*} [MeasurableSpace δ] {F : 𝒴 × γ → δ} (hF : Measurable F)
    (hstop : IsRecordStop stop) {t₀ : ℝ≥0} (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ ρ p) :
    Measurable[ruleMarks stop ρ Y₀ R₀] fun x => F (Y₀ x, stop t₀ (R₀ x)) := by
  have h := hF.comp (measurable_ruleMarks_stopAt_le (Y₀ := Y₀) (R₀ := R₀) hstop hle)
  simpa only [Function.comp_def, stopAt_coe] using h

omit mX in
/-- **The chart read from the time-`0` record is a measurable chart for the rule marks.** -/
theorem isMeasChart_ruleMarks_of_time0 {c : 𝒴 × γ → Chart} (hc : IsMeasChart c) (hstop : IsRecordStop stop)
    {t₀ : ℝ≥0} (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ ρ p) :
    @IsMeasChart X (ruleMarks stop ρ Y₀ R₀) fun x => c (Y₀ x, stop t₀ (R₀ x)) := by
  have hm := measurable_ruleMarks_of_time0 (Y₀ := Y₀) (R₀ := R₀) measurable_id hstop hle
  exact @IsMeasChart.mk X (ruleMarks stop ρ Y₀ R₀) _ (fun z => hm (hc.dom z)) (fun z => (hc.fwd z).comp hm)
    (fun z => (hc.lift z).comp hm)

end Time0

section ChartNull

variable {X : Type*} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X] {μ : Measure X}

/-- **A chart almost surely equal to a chart measurable for `ℋ` is measurable for its null completion.** -/
theorem isMeasChart_nullMarks_of_ae_eq {c c' : X → Chart}
    (hc : IsMeasChart c) (hc' : @IsMeasChart X ℋ c') (he : ∀ᵐ x ∂μ, c x = c' x) :
    @IsMeasChart X (nullMarks ℋ μ) c := by
  refine @IsMeasChart.mk X (nullMarks ℋ μ) c (fun z => ?_) (fun z => ?_) (fun z => ?_)
  · refine measurableSet_nullMarks_of_ae_eq (hc.dom z) (@IsMeasChart.dom X ℋ c' hc' z) ?_
    filter_upwards [he] with x hx
    simp only [hx]
  · refine measurable_nullMarks_of_ae_eq (hc.fwd z) (@IsMeasChart.fwd X ℋ c' hc' z) ?_
    filter_upwards [he] with x hx
    classical
    rw [indicator_apply, indicator_apply]
    simp only [mem_ofPred_eq]
    simp only [hx]
  · refine measurable_nullMarks_of_ae_eq (hc.lift z) (@IsMeasChart.lift X ℋ c' hc' z) ?_
    filter_upwards [he] with x hx
    classical
    rw [indicator_apply, indicator_apply]
    simp only [mem_ofPred_eq]
    simp only [hx]

end ChartNull

/-! ### Almost sure functions of the time-`0` record in the completed marks -/

section Time0Null

variable {X 𝒴 γ : Type*} [mX : MeasurableSpace X] [m𝒴 : MeasurableSpace 𝒴] [mγ : MeasurableSpace γ]
  {stop : ℝ≥0 → γ → γ} {ρ : 𝒴 × γ → ℝ≥0∞} {Y₀ : X → 𝒴} {R₀ : X → γ} {μ : Measure X}

/-- **An almost sure function of the time-`0` record is measurable for the completed rule marks** (the history `Z`,
the event's indicator, a chart coordinate — each read almost surely from `(Y₀, stop t₀ R₀)`). -/
theorem measurable_nullRuleMarks_of_time0_ae {δ : Type*} [MeasurableSpace δ] {f : X → δ} (hf : Measurable f)
    {F : 𝒴 × γ → δ} (hF : Measurable F) (hstop : IsRecordStop stop) {t₀ : ℝ≥0} (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ ρ p)
    (he : ∀ᵐ x ∂μ, f x = F (Y₀ x, stop t₀ (R₀ x))) : Measurable[nullMarks (ruleMarks stop ρ Y₀ R₀) μ] f :=
  measurable_nullMarks_of_ae_eq hf (measurable_ruleMarks_of_time0 hF hstop hle) he

/-- **An event almost surely read from the time-`0` record is in the completed rule marks.** -/
theorem measurableSet_nullRuleMarks_of_time0_ae {E : Set X} (hE : MeasurableSet E) {Er : Set (𝒴 × γ)}
    (hEr : MeasurableSet Er) (hstop : IsRecordStop stop) {t₀ : ℝ≥0} (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ ρ p)
    (he : ∀ᵐ x ∂μ, (x ∈ E ↔ (Y₀ x, stop t₀ (R₀ x)) ∈ Er)) :
    MeasurableSet[nullMarks (ruleMarks stop ρ Y₀ R₀) μ] E := by
  refine measurableSet_nullMarks_of_ae_eq hE
    (measurable_ruleMarks_of_time0 (Y₀ := Y₀) (R₀ := R₀) measurable_id hstop hle hEr) ?_
  filter_upwards [he] with x hx
  exact propext hx

/-- **A chart almost surely read from the time-`0` record is a measurable chart for the completed rule marks.** -/
theorem isMeasChart_nullRuleMarks_of_time0_ae {c : X → Chart} (hc : IsMeasChart c) {cr : 𝒴 × γ → Chart}
    (hcr : IsMeasChart cr) (hstop : IsRecordStop stop) {t₀ : ℝ≥0} (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ ρ p)
    (he : ∀ᵐ x ∂μ, c x = cr (Y₀ x, stop t₀ (R₀ x))) :
    @IsMeasChart X (nullMarks (ruleMarks stop ρ Y₀ R₀) μ) c :=
  isMeasChart_nullMarks_of_ae_eq hc (isMeasChart_ruleMarks_of_time0 hcr hstop hle) he

omit mX m𝒴 mγ in
/-- SLITW's rule interface (`rule 0 = t₀`, `rule 0 ≤ rule q`) gives the lower bound of every rule by the restart
time. -/
theorem le_rule_of_zero {rule : ℝ≥0 → 𝒴 × γ → ℝ≥0∞} {t₀ : ℝ≥0} (h0 : ∀ p, rule 0 p = t₀)
    (hmono : ∀ q p, rule 0 p ≤ rule q p) (q : ℝ≥0) (p : 𝒴 × γ) : (t₀ : ℝ≥0∞) ≤ rule q p :=
  (h0 p) ▸ hmono q p

end Time0Null

/-! ### The record readers of the flow -/

section Readers

variable {nL nR : ℕ}

/-- The driving state read at a time `≤ t₀` only uses the record stopped at `t₀`. -/
theorem histState_stopRec_of_le {t t₀ : ℝ≥0} (ht : t ≤ t₀) (g : HistorySpace nL nR) :
    histState (stopRec t₀ g) t = histState g t := by
  refine histState_congr fun p hp => ?_
  simp only [stopRec, Sec4.stopHistory, ite_eq_left_iff]
  exact fun h => absurd (hp.trans ht) h

/-- The trace read at a time `≤ t₀` only uses the record stopped at `t₀`. -/
theorem histTrace_stopRec_of_le {t t₀ : ℝ≥0} (ht : t ≤ t₀) (y : ℝ) (g : HistorySpace nL nR) :
    histTrace y (stopRec t₀ g) t = histTrace y g t := by
  unfold histTrace
  rw [LP.traceAt_congr fun r hr => congrArg Prod.fst (histState_stopRec_of_le (hr.trans ht) g)]

variable {X 𝒴 : Type*} [mX : MeasurableSpace X] [m𝒴 : MeasurableSpace 𝒴]
  {ρ : 𝒴 × HistorySpace nL nR → ℝ≥0∞} {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR}

omit mX in
/-- **The driving state read at a time `≤ t₀` is recorded by the rule marks** (for a rule at least `t₀`). -/
theorem measurable_ruleMarks_histState {t t₀ : ℝ≥0} (ht : t ≤ t₀) (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ ρ p) :
    Measurable[ruleMarks stopRec ρ Y₀ R₀] fun x => histState (R₀ x) t := by
  have h := measurable_ruleMarks_of_time0 (Y₀ := Y₀) (R₀ := R₀)
    ((measurable_histState (nL := nL) (nR := nR) t).comp measurable_snd) isRecordStop_stopRec hle
  simpa only [Function.comp_def, histState_stopRec_of_le ht] using h

omit mX in
/-- **The trace read at a time `≤ t₀` is recorded by the rule marks** (for a rule at least `t₀`). -/
theorem measurable_ruleMarks_histTrace {t t₀ : ℝ≥0} (ht : t ≤ t₀) (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ ρ p) (y : ℝ) :
    Measurable[ruleMarks stopRec ρ Y₀ R₀] fun x => histTrace y (R₀ x) t := by
  have h := measurable_ruleMarks_of_time0 (Y₀ := Y₀) (R₀ := R₀)
    ((measurable_histTrace (nL := nL) (nR := nR) y t).comp measurable_snd) isRecordStop_stopRec hle
  simpa only [Function.comp_def, histTrace_stopRec_of_le ht] using h

end Readers

/-! ### The readers on a space carrying the flow's coupling -/

section Coupling

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {Bm : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {β : Type*} [MeasurableSpace β] {μ : Measure (Ω × β)}

/-- **The read driving state is the driving state** almost surely (on a space whose first marginal is `P`), before
the lifetime. -/
theorem ae_histState_killedHistory (hev : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR Bm ζ)
    (hμ : μ.map Prod.fst = P) :
    ∀ᵐ p ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ p.1 →
      histState (killedHistory W VL VR ζ p.1) t = (W t p.1, fun i => VL i t p.1, fun j => VR j t p.1) := by
  have h : ∀ᵐ ω ∂(μ.map Prod.fst), ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      histState (killedHistory W VL VR ζ ω) t = (W t ω, fun i => VL i t ω, fun j => VR j t ω) := by
    rw [hμ]
    filter_upwards [hev.2.2.2.2] with ω hp t ht
    exact histState_killedHistory (hp.2.2.2.1.prodMk ((continuousOn_pi.2 hp.2.2.2.2.1).prodMk
      (continuousOn_pi.2 hp.2.2.2.2.2.1))) ht
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- **The read trace is the generating trace** almost surely (on a space whose first marginal is `P`), before the
lifetime. -/
theorem ae_histTrace_killedHistory (hev : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR Bm ζ)
    {η : Ω → ℝ≥0 → ℂ} (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - ((0 : ℝ) : ℂ)))
    (hμ : μ.map Prod.fst = P) :
    ∀ᵐ p ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ p.1 → histTrace 0 (killedHistory W VL VR ζ p.1) t = η p.1 t := by
  have h : ∀ᵐ ω ∂(μ.map Prod.fst), ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      histTrace 0 (killedHistory W VL VR ζ ω) t = η ω t := by
    rw [hμ]
    filter_upwards [hev.2.2.2.2, htr] with ω hp hg t ht
    exact histTrace_killedHistory (hp.2.2.2.1.prodMk ((continuousOn_pi.2 hp.2.2.2.2.1).prodMk
      (continuousOn_pi.2 hp.2.2.2.2.2.1))) hp.1 hg ht
  exact ae_of_ae_map measurable_fst.aemeasurable h

/-- **R1's measurable own driver / trace / observation inputs for the rule marks** (`hY`, `hUm`, `hm` of
`Aux61Restart.has_original_target_restart_chart_of_protection`, with the record-read driver and trace): on a space
`Ω × β` carrying the flow's coupling in its first coordinate, with records `Y₀ = stopRec s ∘ snd` (the counterflow) and
`R₀ = killedHistory ∘ fst` (the flow), for every rule at least the restart time `t₀`: the stopped counterflow record
and the read driving state and trace at times `≤ t₀` are measurable for the rule marks, and almost surely they are the
flow's driving state and generating trace before the lifetime. -/
theorem recordInputs_of_coupling (hev : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR Bm ζ)
    {η : Ω → ℝ≥0 → ℂ} (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - ((0 : ℝ) : ℂ)))
    {μ' : Measure (Ω × HistorySpace 0 0)} (hμ : μ'.map Prod.fst = P) (s : ℝ≥0)
    {rule : HistorySpace 0 0 × HistorySpace nL nR → ℝ≥0∞} {t₀ : ℝ≥0} (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ rule p) :
    Measurable[ruleMarks stopRec rule (fun p : Ω × HistorySpace 0 0 => stopRec s p.2)
      (fun p => killedHistory W VL VR ζ p.1)] (fun p : Ω × HistorySpace 0 0 => GlueCond.cfStop s p.2) ∧
    (∀ t ≤ t₀, Measurable[ruleMarks stopRec rule (fun p : Ω × HistorySpace 0 0 => stopRec s p.2)
      (fun p => killedHistory W VL VR ζ p.1)] fun p => histState (killedHistory W VL VR ζ p.1) t) ∧
    (∀ t ≤ t₀, Measurable[ruleMarks stopRec rule (fun p : Ω × HistorySpace 0 0 => stopRec s p.2)
      (fun p => killedHistory W VL VR ζ p.1)] fun p => histTrace 0 (killedHistory W VL VR ζ p.1) t) ∧
    (∀ᵐ p ∂μ', ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ p.1 →
      histState (killedHistory W VL VR ζ p.1) t = (W t p.1, fun i => VL i t p.1, fun j => VR j t p.1)) ∧
    ∀ᵐ p ∂μ', ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ p.1 → histTrace 0 (killedHistory W VL VR ζ p.1) t = η p.1 t := by
  refine ⟨?_, fun t ht => measurable_ruleMarks_histState ht hle, fun t ht => measurable_ruleMarks_histTrace ht hle 0,
    ae_histState_killedHistory hev hμ, ae_histTrace_killedHistory hev htr hμ⟩
  have h := measurable_ruleMarks_of_factor (stop := stopRec) (ρ := rule)
    (Y₀ := fun p : Ω × HistorySpace 0 0 => stopRec s p.2) (R₀ := fun p => killedHistory W VL VR ζ p.1)
    (measurable_fst : Measurable fun q : HistorySpace 0 0 × HistorySpace nL nR => q.1)
  exact h

end Coupling

/-! ### The raw code in the completed marks -/

section Code

variable {X : Type u} {ℋ : MeasurableSpace X} [mX : MeasurableSpace X] {μ : Measure X}

/-- **The raw code σ-algebra at `r` lies in the completed marks** if the code agrees almost surely up to `r` with a code
measurable for the marks: the same aliveness at every `r' ≤ r`, and the same driver while alive. -/
theorem codeFiltration_le_nullMarks_of_ae_agree {Y F : X → Aux61Fib.FibCode} {r : ℝ≥0} (hY : Measurable Y)
    (hF : Measurable[ℋ] F)
    (hagree : ∀ᵐ x ∂μ, ∀ r' ≤ r, ((((r' : ℝ≥0) : ℝ≥0∞) < (Y x).life ↔ ((r' : ℝ≥0) : ℝ≥0∞) < (F x).life) ∧
      (((r' : ℝ≥0) : ℝ≥0∞) < (Y x).life → Aux61Fib.FibCode.driver r' (Y x) = Aux61Fib.FibCode.driver r' (F x)))) :
    (Aux61FibK.codeFiltration.{u} r).comap (fun x => ULift.up.{u} (Y x)) ≤ nullMarks ℋ μ := by
  refine codeFiltration_comap_le_nullMarks fun r' hr' A hA => ?_
  have hm : ∀ {m : MeasurableSpace X} {Z : X → Aux61Fib.FibCode}, Measurable[m] Z →
      MeasurableSet[m] {x | ((r' : ℝ≥0) : ℝ≥0∞) < (Z x).life ∧
        (Aux61Fib.FibCode.driver r' (Z x), (fun _ : Fin 0 => (0 : ℝ)), fun _ : Fin 0 => (0 : ℝ)) ∈ A} := by
    intro m Z hZ
    refine (measurableSet_lt measurable_const (Aux61Fib.FibCode.measurable_life.comp hZ)).inter ?_
    exact (((Aux61Fib.FibCode.measurable_driver r').comp hZ).prodMk (measurable_const.prodMk measurable_const)) hA
  refine measurableSet_nullMarks_of_ae_eq (hm hY) (hm hF) ?_
  filter_upwards [hagree] with x hx
  obtain ⟨hl, hd⟩ := hx r' hr'
  refine propext ⟨fun h => ⟨hl.1 h.1, ?_⟩, fun h => ⟨hl.2 h.1, ?_⟩⟩
  · rw [← hd h.1]
    exact h.2
  · rw [hd (hl.2 h.1)]
    exact h.2

end Code

end InteractingSLE.Sec5.Aux61Marks
