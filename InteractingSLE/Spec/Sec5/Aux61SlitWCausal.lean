/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWRead
import InteractingSLE.Spec.Sec5.Aux61SlitWFirstHit

/-!
# The causal capacity rule of a retained restart chart

The chart is read from the initial retained record. Every subsequent
capacity decision uses only samples at or before the current physical time.
The rule is uncapped; agreement with the selected-access inverse clock is
proved on the event where that code is alive.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open LawUnique Aux61ULoc Aux61FibData Restart.FlowStopIdentG

variable {Y : Type*} [MeasurableSpace Y] {nL nR : ℕ}

/-- A positive-time chart point read from the initial chart and current own prefix. -/
def prefixPoint (c : Y × HistorySpace nL nR → Chart) (r : ℝ≥0)
    (y : Y) (g : HistorySpace nL nR) (u : ℝ≥0) : ℂ :=
  if u = 0 then 0 else readChart (c (y, stopRec r g)) (histTrace 0 g (r + u))

/-- Dyadic samples of the chart prefix visible at physical time `t`. -/
def prefixSample (c : Y × HistorySpace nL nR → Chart) (r : ℝ≥0)
    (p : Y × HistorySpace nL nR) (t : ℝ≥0) (j : ℕ × ℕ) : ℂ :=
  if t < r then 0 else prefixPoint c r p.1 p.2 (min (dyadicTime j) (t - r))

/-- Grid capacity of precisely the chart prefix visible at the current time. -/
def prefixCapacity (c : Y × HistorySpace nL nR → Chart) (r : ℝ≥0)
    (p : Y × HistorySpace nL nR) (t : ℝ≥0) : ℝ :=
  (WholeField.hcapHit (closure (range (prefixSample c r p t)))).toReal / 2

theorem measurable_prefixCapacity {c : Y × HistorySpace nL nR → Chart}
    (hc : IsMeasChart c) (r t : ℝ≥0) : Measurable fun p => prefixCapacity c r p t := by
  have hR : Measurable fun p : Y × HistorySpace nL nR => (p.1, stopRec r p.2) :=
    measurable_fst.prodMk (isRecordStop_stopRec.measurable.comp (measurable_const.prodMk measurable_snd))
  have hc' : IsMeasChart (fun p : Y × HistorySpace nL nR => c (p.1, stopRec r p.2)) :=
    ⟨fun z => hR (hc.dom z), fun z => (hc.fwd z).comp hR, fun z => (hc.lift z).comp hR⟩
  apply Measurable.div_const
  apply Measurable.ennreal_toReal
  apply WholeField.measurable_hcapHit.comp
  apply measurable_closure_range
  intro j
  unfold prefixSample prefixPoint
  refine Measurable.ite (MeasurableSet.const _) measurable_const ?_
  refine Measurable.ite (MeasurableSet.const _) measurable_const ?_
  exact measurable_readChart hc' ((measurable_histTrace 0 _).comp measurable_snd)

/-- Reading the trace at any time uses only the own samples up to that time. -/
theorem histTrace_eq_of_prefix {g g' : HistorySpace nL nR} {t : ℝ≥0}
    (h : ∀ p, dyadicTime p ≤ t → g.2 p = g'.2 p) : histTrace 0 g t = histTrace 0 g' t := by
  unfold histTrace
  rw [LP.traceAt_congr fun u hu => congrArg Prod.fst
    (histState_congr fun p hp => h p (hp.trans hu))]

/-- The initial chart and every capacity sample are fixed by the available own prefix. -/
theorem isNonAnticipating_prefixCapacity (c : Y × HistorySpace nL nR → Chart) (r : ℝ≥0) (y : Y) :
    IsNonAnticipating (fun g t => prefixCapacity c r (y, g) t) := by
  intro g g' p h
  change prefixCapacity c r (y, g) (dyadicTime p) = prefixCapacity c r (y, g') (dyadicTime p)
  by_cases ht : dyadicTime p < r
  · have hs : prefixSample c r (y, g) (dyadicTime p) = prefixSample c r (y, g') (dyadicTime p) :=
      funext fun j => by simp only [prefixSample, ht, ↓reduceIte]
    unfold prefixCapacity
    rw [hs]
  have hr : r ≤ dyadicTime p := not_lt.1 ht
  have he : stopRec r g = stopRec r g' := by
    refine Prod.ext rfl (funext fun j => ?_)
    simp only [stopRec, Sec4.stopHistory]
    by_cases hj : dyadicTime j ≤ r
    · rw [ite_eq_left hj, ite_eq_left hj, h j (hj.trans hr)]
    · rw [ite_eq_right hj, ite_eq_right hj]
  have hs : prefixSample c r (y, g) (dyadicTime p) = prefixSample c r (y, g') (dyadicTime p) := by
    funext j
    simp only [prefixSample, ht, ↓reduceIte, prefixPoint, he]
    by_cases hj : min (dyadicTime j) (dyadicTime p - r) = 0
    · rw [ite_eq_left hj, ite_eq_left hj]
    rw [ite_eq_right hj, ite_eq_right hj]
    congr 1
    apply histTrace_eq_of_prefix
    intro k hk
    apply h k
    apply hk.trans
    calc
      r + min (dyadicTime j) (dyadicTime p - r) ≤ r + (dyadicTime p - r) := by
        gcongr
        exact min_le_right _ _
      _ = dyadicTime p := add_tsub_cancel_of_le hr
  simp only [prefixCapacity, hs]

/-- Physical code time: the first observed capacity hit, with time zero
of the restart identified with its original physical start. -/
def capacityRule (c : Y × HistorySpace nL nR → Chart) (r q : ℝ≥0)
    (p : Y × HistorySpace nL nR) : ℝ≥0∞ :=
  if q = 0 then r else
    max (hitRule (fun g t => prefixCapacity c r (p.1, g) t) (Ici (q : ℝ)) (fullRecord p.2)) r

theorem measurable_capacityRule {c : Y × HistorySpace nL nR → Chart} (hc : IsMeasChart c)
    (r q : ℝ≥0) : Measurable (capacityRule c r q) := by
  unfold capacityRule
  refine Measurable.ite (MeasurableSet.const _) measurable_const ?_
  apply Measurable.max _ measurable_const
  refine measurable_param_hitRule (measurable_fullRecord.comp measurable_snd) (fun p => ?_) _
  exact (measurable_prefixCapacity hc r _).comp
    (measurable_fst.prodMk (measurable_fullRecord.comp measurable_snd))

/-- The actual prefix-capacity decisions define a Galmarino rule. -/
theorem isGalmarinoRule_capacityRule (c : Y × HistorySpace nL nR → Chart) (r q : ℝ≥0) :
    IsGalmarinoRule stopRec (capacityRule c r q) := by
  by_cases hq : q = 0
  · intro y g t _
    simp only [capacityRule, hq, ↓reduceIte]
  · intro y g t h
    simp only [capacityRule, hq, ↓reduceIte] at h ⊢
    exact isGalmarinoRule_max
      (isGalmarinoRule_firstHit (fun y g t => prefixCapacity c r (y, g) t)
        (isNonAnticipating_prefixCapacity c r) (Ici (q : ℝ))) r y g t h

theorem capacityRule_zero (c : Y × HistorySpace nL nR → Chart) (r : ℝ≥0)
    (p : Y × HistorySpace nL nR) : capacityRule c r 0 p = r := by
  simp only [capacityRule, ↓reduceIte]

theorem start_le_capacityRule (c : Y × HistorySpace nL nR → Chart) (r q : ℝ≥0)
    (p : Y × HistorySpace nL nR) : (r : ℝ≥0∞) ≤ capacityRule c r q p := by
  unfold capacityRule
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

/-- The rule retains all information used to select its initial chart and window. -/
theorem initial_ruleMarks_le {X : Type*} (c : Y × HistorySpace nL nR → Chart)
    (r q : ℝ≥0) (Y₀ : X → Y) (R₀ : X → HistorySpace nL nR) :
    ruleMarks stopRec (fun _ => (r : ℝ≥0∞)) Y₀ R₀ ≤ ruleMarks stopRec (capacityRule c r q) Y₀ R₀ :=
  Aux61Nest.ruleMarks_mono isRecordStop_stopRec measurable_const (fun _ _ _ _ => rfl)
    (fun y g => start_le_capacityRule c r q (y, g)) Y₀ R₀

end InteractingSLE.Sec5.Aux61SlitW
