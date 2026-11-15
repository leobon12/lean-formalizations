/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61SlitWCausal
import InteractingSLE.Spec.Sec5.Aux61SlitWClock

/-! # The prefix-capacity reader equals the selected-access clock -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitW
open LawUnique Aux61ULoc Aux61FibData Aux61GInst Restart
open Restart.FlowStopIdentG

variable {Y : Type*} [MeasurableSpace Y] {nL nR : ℕ}

theorem stopRec_fullRecord (r : ℝ≥0) (g : HistorySpace nL nR) :
    stopRec r (fullRecord g) = stopRec r g := rfl

theorem histTrace_fullRecord (g : HistorySpace nL nR) (t : ℝ≥0) :
    histTrace 0 (fullRecord g) t = histTrace 0 g t := rfl

/-- Before the restart the observed chart prefix is the singleton at its origin. -/
theorem prefixCapacity_eq_start (c : Y × HistorySpace nL nR → Chart)
    (r : ℝ≥0) (p : Y × HistorySpace nL nR) {t : ℝ≥0} (ht : t ≤ r) :
    prefixCapacity c r p t = prefixCapacity c r p r := by
  have hs : ∀ s ≤ r, prefixSample c r p s = fun _ => 0 := by
    intro s hsr
    funext j
    unfold prefixSample
    split_ifs
    · rfl
    · simp only [tsub_eq_zero_of_le hsr, min_zero, prefixPoint, ↓reduceIte]
  unfold prefixCapacity
  rw [hs t ht, hs r le_rfl]

section Access
variable {X : Type*} [MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  {x : X} (hx : x ∈ exitEv E cc ρ T V)
  {c : Y × HistorySpace nL nR → Chart} {r : ℝ≥0} {y : Y} {g : HistorySpace nL nR}
  (hchart : cc x = c (y, stopRec r g))
  (hρ : ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 g (r + u))

include hs hV hV0 hland hx hchart hρ

/-- Each actual chart point strictly before the selected exit is read from
the initial chart and the physical own prefix available at that point. -/
theorem prefixPoint_eq_accessPath {u : ℝ≥0} (hu : u < exitNN E cc ρ T V x) :
    prefixPoint c r y (fullRecord g) u = accessExitPath E cc ρ T V x u := by
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  by_cases hu0 : u = 0
  · rw [hu0, hp.zero x hx]
    simp only [prefixPoint, ↓reduceIte]
  have hu' : 0 < u := pos_iff_ne_zero.2 hu0
  have huT : (u : ℝ≥0∞) < T x := (ENNReal.coe_lt_coe.2 hu).trans_le
    (IsRestartSpec.coe_exitNN hx ▸ IsRestartSpec.exitTime_le x)
  rw [prefixPoint, ite_eq_right hu0, stopRec_fullRecord, histTrace_fullRecord,
    ← hchart, ← hρ u hu' hu, readChart_eq (hs.conf x hx.1.1) (hs.inside x hx.1.1 u hu' huT)]
  rw [accessExitPath, ite_eq_left hx, ite_eq_left hu, hs.inPath_eq_fwd hx.1.1 hu' huT]

/-- Before the selected exit, the countable prefix reader is exactly the
capacity clock used by the actual selected-access code. -/
theorem prefixCapacity_eq_accessClock {v : ℝ≥0} (hv : v < exitNN E cc ρ T V x) :
    prefixCapacity c r (y, fullRecord g) (r + v) =
      capClock (exitEv E cc ρ T V) (accessExitPath E cc ρ T V) (exitNN E cc ρ T V) x v := by
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have he : prefixSample c r (y, fullRecord g) (r + v) =
      fun j => accessExitPath E cc ρ T V x (min (dyadicTime j) v) := by
    funext j
    simp only [prefixSample, not_lt.2 (le_self_add : r ≤ r + v), ↓reduceIte, add_tsub_cancel_left]
    exact prefixPoint_eq_accessPath hs hV hV0 hland hx hchart hρ ((min_le_right _ _).trans_lt hv)
  unfold prefixCapacity
  rw [he, closure_range_clamped_dyadic
    ((hp.cont x hx).mono (fun u hu => hu.2.trans hv.le))]
  rw [capClock, ite_eq_left hx, image_clampPath hx hv.le]

end Access

section RuleValue
variable {X : Type*} [MeasurableSpace X] {E : Set X} {cc : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞} {V : Set ℂ}
  (hs : IsRestartSpec E cc ρ T) (hV : IsOpen V) (hV0 : (0 : ℂ) ∈ V)
  (hland : HasAccessLanding E cc ρ T V)
  (hinj : ∀ x ∈ E, InjOn (ρ x) {u | (u : ℝ≥0∞) < T x})
  {a k : ℝ} {h : X → LQGMetric.DistOn upperHalfPlaneOpens}
  {c : Y × HistorySpace nL nR → Chart} {r : ℝ≥0} {y : Y} {g : HistorySpace nL nR}
  {x : X} (hchart : cc x = c (y, stopRec r g))
  (hρ : ∀ u : ℝ≥0, 0 < u → u < exitNN E cc ρ T V x → ρ x u = histTrace 0 g (r + u))

include hs hV hV0 hland hinj hchart hρ

/-- The causal capacity rule is exactly the actual physical time of the
selected-access code, whenever that code is alive at a positive chart time. -/
theorem capacityRule_eq_accessTime {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < (accessExitCode E cc ρ T V a k h x).life) :
    capacityRule c r q (y, g) =
      ((r + accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x q : ℝ≥0) : ℝ≥0∞) := by
  have hx := mem_exitEv_of_lt_accessLife hq
  have hp := isPathSpec_accessExitPath hs hV hV0 hland
  have hclk := isClockOn_accessExitPath hs hV hV0 hland hinj
  have hcl := hp.isClockOn_capClock hclk hx
  let τ := accessTime (E := E) (c := cc) (ρ := ρ) (T := T) (V := V) x q
  have hτ : τ < exitNN E cc ρ T V x := (accessTime_spec hs hV hV0 hland hinj hq).1
  have hτ0 : 0 < τ := accessTime_pos hs hV hV0 hland hinj hq hq0
  let C := capClock (exitEv E cc ρ T V) (accessExitPath E cc ρ T V) (exitNN E cc ρ T V) x
  have hCτ : C τ = q := (accessTime_spec hs hV hV0 hland hinj hq).2
  have hobs : ∀ s ≤ r + τ, prefixCapacity c r (y, fullRecord g) s = C (s - r) := by
    intro s hs'
    by_cases hrs : r ≤ s
    · have hv : s - r ≤ τ := (tsub_le_iff_right).2 (by simpa only [add_comm τ r] using hs')
      have he := prefixCapacity_eq_accessClock hs hV hV0 hland hx hchart hρ (hv.trans_lt hτ)
      rwa [add_tsub_cancel_of_le hrs] at he
    · have he := prefixCapacity_eq_accessClock hs hV hV0 hland hx hchart hρ
        ((hτ0.trans hτ) : 0 < exitNN E cc ρ T V x)
      rw [prefixCapacity_eq_start c r _ (not_le.1 hrs).le, tsub_eq_zero_of_le (not_le.1 hrs).le]
      simpa only [add_zero] using he
  have he : hitRule (fun g t => prefixCapacity c r (y, g) t) (Ici (q : ℝ)) (fullRecord g) =
      ((r + τ : ℝ≥0) : ℝ≥0∞) := by
    apply firstHit_eq_of_hit (isNonAnticipating_prefixCapacity c r y) isClosed_Ici
      (hτ0.trans_le le_add_self)
      (((hp.continuous_capClock hclk x).comp (continuous_id.sub continuous_const)).continuousOn)
    · intro s hs'
      show ¬ (q : ℝ) ≤ C (s - r)
      have hv : s - r < τ := by
        by_cases hrs : r ≤ s
        · exact (tsub_lt_iff_left hrs).2 hs'
        · rw [tsub_eq_zero_of_le (not_le.1 hrs).le]
          exact hτ0
      rw [← hCτ]
      exact not_le.2 (hcl.strictMonoOn (ENNReal.coe_le_coe.2 (hv.le.trans hτ.le))
        (ENNReal.coe_le_coe.2 hτ.le) hv)
    · show (q : ℝ) ≤ C (r + τ - r)
      rw [add_tsub_cancel_left, hCτ]
    · intro p hp'
      exact hobs _ (ENNReal.coe_lt_coe.1 hp').le
  simp only [capacityRule, hq0.ne', ↓reduceIte, he,
    max_eq_left (ENNReal.coe_le_coe.2 (le_self_add : r ≤ r + τ))]
  rfl

end RuleValue

end InteractingSLE.Sec5.Aux61SlitW
