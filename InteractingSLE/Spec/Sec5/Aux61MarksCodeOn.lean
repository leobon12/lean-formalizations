/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61MarksAlive
import InteractingSLE.Spec.Sec5.Aux61MarksContact

/-!
# `code_le` from record readings on the restart event only

Packet PROVE-AUX61-MARKS. The `code_le` theorems of `Aux61MarksCode`/`Aux61MarksAlive` take the record readings almost
surely on the whole space. The concrete restart's path and contact are only specified on its event `E` (off `E` they are
junk), so here the readings are required **almost surely on `E` only**:

* `ae_driver_eq_recDriver_on`, `measurableSet_alive_nullRuleMarks_on`, `codeFiltration_le_nullRuleMarks_of_record_on`:
  the driver half, the aliveness events and `code_le` with the readings on `E` (an alive code lives on `E`);
* **`codeFiltration_le_nullRuleMarks_of_source`**: `code_le` for the concrete source form — the chart read from the
  time-`0` record (the chart clause is definitional), the event a version of a record event `{record ∈ B}`, on which
  the restart almost surely stops (a finite contact or a window exit), the restarted path the record's trace before the
  contact, and the contact the first hitting time of a closed obstacle read from the records at `t₀`. The absolute
  contact time is then SLITW's first-hit rule `contactRule` (`Aux61MarksContact`), a measurable Galmarino rule.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Marks

open Aux61ULoc LawUnique Restart.FlowStopIdentG Aux61FibData Aux61GInst Aux61Fib
open Aux61SlitW (capacityRule)

universe u

section On

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

/-- The driver half of `code_le` with the record readings on the event only. -/
theorem ae_driver_eq_recDriver_on (hc : IsMeasChart c) (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) (r : ℝ≥0)
    (hrec : ∀ᵐ x ∂μ, x ∈ E → cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) (r' : ℝ≥0)
    (hr' : r' ≤ r) :
    ∃ D : X → ℝ, Measurable[ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀] D ∧
      ∀ᵐ x ∂μ, ((r' : ℝ≥0) : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life →
        FibCode.driver r' (accessExitCode E cc ρ T V a k h x) = D x := by
  refine ⟨fun x => recDriver c t₀ r' (Y₀ x, stopAt stopRec (capacityRule c t₀ r (Y₀ x, R₀ x)) (R₀ x)),
    measurable_ruleMarks_of_factor (measurable_recDriver hc t₀ r'), ?_⟩
  filter_upwards [hrec] with x hx halive
  have hxE : x ∈ E := (mem_exitEv_of_lt_accessLife halive).1.1
  exact driver_eq_recDriver_stopAt hs hV hV0 hland hinj (hx hxE).1 (hx hxE).2 d hdV hℓ halive hr'

/-- The aliveness events in the completed rule marks, with the record readings on the event only. -/
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
  · exact hxE ▸ (mem_exitEv_of_lt_accessLife halive).1.1
  · have hxe : x ∈ E := (mem_exitEv_of_lt_accessLife halive).1.1
    obtain ⟨hch, hρx, hTax⟩ := hx hxe
    exact hstop.2 (aliveRec_of_alive hs hV hV0 hland hinj hch hρx hTax halive hrr)
  · have hxe : x ∈ E := hxE ▸ hJ.1
    obtain ⟨hch, hρx, hTax⟩ := hx hxe
    exact alive_of_aliveRec hs hV hV0 hland hinj hch hρx hTax (hexx hxe) (hstop.1 hJ.2)

/-- **`code_le` for the completed rule marks, with the record readings on the event only.** -/
theorem codeFiltration_le_nullRuleMarks_of_record_on (hc : IsMeasChart c) (hTam : Measurable Ta)
    (hTaG : IsGalmarinoRule stopRec Ta) (hliftc : ∀ x ∈ E, ContinuousOn (cc x).2.2 (cc x).dom)
    (hh : Measurable h) (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) (r : ℝ≥0)
    (hE : MeasurableSet[nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ] E)
    (hrec : ∀ᵐ x ∂μ, x ∈ E → cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      (∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u)) ∧
      Ta (Y₀ x, R₀ x) = (t₀ : ℝ≥0∞) + T x)
    (hexit : ∀ᵐ x ∂μ, x ∈ E → x ∈ exitEv E cc ρ T V) :
    (Aux61FibK.codeFiltration.{u} r).comap (fun x => ULift.up.{u} (accessExitCode E cc ρ T V a k h x)) ≤
      nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ := by
  have hrec' : ∀ᵐ x ∂μ, x ∈ E → cc x = c (Y₀ x, stopRec t₀ (R₀ x)) ∧
      ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 (R₀ x) (t₀ + u) := by
    filter_upwards [hrec] with x hx hxE
    exact ⟨(hx hxE).1, fun u hu hue => (hx hxE).2.1 u hu (lt_T_of_lt_exitNN hue)⟩
  exact codeFiltration_le_nullMarks_of_alive (measurable_accessExitCode hs hV hV0 hland hinj hliftc hh)
    (fun r' hr' => measurableSet_alive_nullRuleMarks_on hs hV hV0 hland hinj hc hTam hTaG hliftc hh hr' hE hrec
      hexit)
    fun r' hr' => ae_driver_eq_recDriver_on hs hV hV0 hland hinj hc d hdV hℓ r hrec' r' hr'

end On

/-! ### The concrete source form -/

section Source

variable {X : Type u} [mX : MeasurableSpace X] {E : Set X} {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {𝒴 : Type*} [MeasurableSpace 𝒴] {nL nR : ℕ}
  {c : 𝒴 × HistorySpace nL nR → Chart} {t₀ : ℝ≥0} {Y₀ : X → 𝒴} {R₀ : X → HistorySpace nL nR} {μ : Measure X}

/-- **The event in the completed marks**: a version of a record event at time `0` is in the null completion of the
rule marks of every rule `≥ t₀`. -/
theorem measurableSet_nullRuleMarks_of_version {rule : 𝒴 × HistorySpace nL nR → ℝ≥0∞}
    (hle : ∀ p, (t₀ : ℝ≥0∞) ≤ rule p) (hEm : MeasurableSet E) {B : Set (𝒴 × HistorySpace nL nR)}
    (hB : MeasurableSet B) (hEv : E =ᵐ[μ] (fun x => (Y₀ x, stopRec t₀ (R₀ x))) ⁻¹' B) :
    MeasurableSet[nullMarks (ruleMarks stopRec rule Y₀ R₀) μ] E :=
  measurableSet_nullMarks_of_ae_eq hEm
    ((measurable_ruleMarks_of_time0 (F := id) measurable_id isRecordStop_stopRec hle) hB) hEv

omit [MeasurableSpace 𝒴] in
/-- **The window exit almost surely on the event**, when the event is a version of a record event on which the
restart almost surely stops: a positive contact, finite or after a window exit. -/
theorem ae_mem_exitEv_of_stop {cc : X → Chart} {B : Set (𝒴 × HistorySpace nL nR)}
    (hEv : E =ᵐ[μ] (fun x => (Y₀ x, stopRec t₀ (R₀ x))) ⁻¹' B)
    (hstop : ∀ᵐ x ∂μ, (Y₀ x, stopRec t₀ (R₀ x)) ∈ B → x ∈ E ∧ 0 < T x ∧
      (T x < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < T x ∧ inPath E cc ρ T x v ∉ V)) :
    ∀ᵐ x ∂μ, x ∈ E → x ∈ exitEv E cc ρ T V := by
  filter_upwards [hEv, hstop] with x hxe hxs hxE
  have hxB : (Y₀ x, stopRec t₀ (R₀ x)) ∈ B := by
    have h : x ∈ (fun x => (Y₀ x, stopRec t₀ (R₀ x))) ⁻¹' B := (show (x ∈ E) = _ from hxe) ▸ hxE
    exact h
  obtain ⟨-, hpos, hst⟩ := hxs hxB
  exact Aux61GCont.mem_exitEv_of_contact_or_exit hxE hpos hst

/-- **`code_le` for the concrete source form.** The chart is read from the time-`0` record; the event is a version of
a record event `{record ∈ B}` on which the restart almost surely stops; the restarted path is, almost surely on the
event, the record's continuous trace after `t₀` before the contact; the contact is the first hitting time of a closed
nonempty obstacle `C` read from the records at `t₀` (with measurable distances) by a path starting off it. Then the raw
code σ-algebra at `r` is in the null completion of the rule marks of SLITW's glued stop `capacityRule c t₀ r`. -/
theorem codeFiltration_le_nullRuleMarks_of_source
    (hs : IsRestartSpec E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
    (hland : HasAccessLanding E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T V)
    (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x}) (hc : IsMeasChart c)
    (hliftc : ∀ x ∈ E, ContinuousOn (c (Y₀ x, stopRec t₀ (R₀ x))).2.2 (c (Y₀ x, stopRec t₀ (R₀ x))).dom)
    (hh : Measurable h) (d : FibData) (hdV : d.V = V) (hℓ : d.ℓ = clr V) (r : ℝ≥0)
    {B : Set (𝒴 × HistorySpace nL nR)} (hB : MeasurableSet B)
    (hEv : E =ᵐ[μ] (fun x => (Y₀ x, stopRec t₀ (R₀ x))) ⁻¹' B)
    (hstop : ∀ᵐ x ∂μ, (Y₀ x, stopRec t₀ (R₀ x)) ∈ B → x ∈ E ∧ 0 < T x ∧
      (T x < ⊤ ∨ ∃ v : ℝ≥0, (v : ℝ≥0∞) < T x ∧
        inPath E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T x v ∉ V))
    (hpath : ∀ᵐ x ∂μ, x ∈ E → ∀ u : ℝ≥0, 0 < u → (u : ℝ≥0∞) < T x → ρ x u = histTrace 0 (R₀ x) (t₀ + u))
    (htr : ∀ᵐ x ∂μ, x ∈ E → Continuous (histTrace 0 (R₀ x)))
    {C : 𝒴 × HistorySpace nL nR → Set ℂ} (hC : ∀ p, IsClosed (C p)) (hCne : ∀ p, (C p).Nonempty)
    (hCm : ∀ z : ℂ, Measurable fun p : 𝒴 × HistorySpace nL nR => infDist z (C p))
    (hT : ∀ᵐ x ∂μ, x ∈ E → T x = hitTime ρ (fun x => C (Y₀ x, stopRec t₀ (R₀ x))) x ∧
      ρ x 0 ∉ C (Y₀ x, stopRec t₀ (R₀ x))) :
    (Aux61FibK.codeFiltration.{u} r).comap (fun x => ULift.up.{u}
      (accessExitCode E (fun x => c (Y₀ x, stopRec t₀ (R₀ x))) ρ T V a k h x)) ≤
      nullMarks (ruleMarks stopRec (capacityRule c t₀ r) Y₀ R₀) μ := by
  have hTa := ae_contactRule_eq hC hCne hs.contρ htr hT hpath
  refine codeFiltration_le_nullRuleMarks_of_record_on hs hV hV0 hland hinj hc (measurable_contactRule hCm t₀)
    (isGalmarinoRule_contactRule C t₀) hliftc hh d hdV hℓ r
    (measurableSet_nullRuleMarks_of_version (Aux61SlitW.start_le_capacityRule c t₀ r) hs.measurableSet hB hEv) ?_
    (ae_mem_exitEv_of_stop hEv hstop)
  filter_upwards [hpath, hTa] with x hx hxT hxE
  exact ⟨rfl, hx hxE, hxT hxE⟩

end Source

end InteractingSLE.Sec5.Aux61Marks
