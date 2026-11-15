/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleAvailable

/-!
# Deterministic prefix consistency of the finite schedule code

Extending the program changes none of its earlier word, field, or driver codes.
Concatenated drivers consequently agree through the earlier terminal time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Prop513TreeExtract StripSideHeightProb

def lastTime : ℝ≥0 → List (ℝ × ℝ≥0) → ℝ≥0
  | a, [] => a
  | _, p :: l => lastTime p.2 l

theorem lastTime_eq_getLast (a : ℝ≥0) (l : List (ℝ × ℝ≥0)) (hl : l ≠ []) :
    lastTime a l = (l.getLast hl).2 := by
  induction l generalizing a with
  | nil => exact False.elim (hl rfl)
  | cons p l ih =>
    cases l with
    | nil => rfl
    | cons q l => exact ih p.2 (List.cons_ne_nil _ _)

theorem terminal_eq_lastTime (s : Schedule) : terminal s = lastTime 0 (scheduleList s) := by
  have hl : scheduleList s ≠ [] := by
    intro he
    exact s.2.1 (List.map_eq_nil_iff.1 he)
  rw [lastTime_eq_getLast _ _ hl]
  simp only [scheduleList, List.getLast_map]
  rfl

theorem scheduleProgram_append (a : ℝ≥0) (l r : List (ℝ × ℝ≥0)) :
    scheduleProgram a (l ++ r) = scheduleProgram a l ++ scheduleProgram (lastTime a l) r := by
  induction l generalizing a with
  | nil => rfl
  | cons p l ih => exact congrArg (List.cons _) (ih p.2)

theorem scheduleProgram_prefix (a : ℝ≥0) {l r : List (ℝ × ℝ≥0)}
    (hlr : l.IsPrefix r) : (scheduleProgram a l).IsPrefix (scheduleProgram a r) := by
  obtain ⟨tail, rfl⟩ := hlr
  exact ⟨scheduleProgram (lastTime a l) tail, (scheduleProgram_append a l tail).symm⟩

theorem lookup_eq_of_prefix {α : Type*} {l r : List α} (hlr : l.IsPrefix r)
    {k : ℕ} (hk : k < l.length) : l[k]? = r[k]? := by
  obtain ⟨tail, rfl⟩ := hlr
  exact (List.getElem?_append_left hk).symm

theorem scheduleList_prefix {s r : Schedule} (hsr : s.1.IsPrefix r.1) :
    (scheduleList s).IsPrefix (scheduleList r) := by
  obtain ⟨tail, he⟩ := hsr
  exact ⟨tail.map (fun p =>
    (if p.1 then Real.pi / 2 else -(Real.pi / 2), (p.2 : ℝ).toNNReal)), by
      change (s.1.map _ ++ tail.map _) = r.1.map _
      rw [← List.map_append, he]⟩

theorem codeContext_prefix (h44 : Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord)
    {s r : Schedule} (hsr : s.1.IsPrefix r.1) (f : DistOn upperHalfPlaneOpens) :
    ∀ k, k ≤ (scheduleSpec s).2.2.length →
      codeContext h44 hκ hκ4 c (scheduleSpec s) k f =
        codeContext h44 hκ hκ4 c (scheduleSpec r) k f
  | 0, _ => rfl
  | k + 1, hk => by
    have he := lookup_eq_of_prefix (scheduleProgram_prefix 0 (scheduleList_prefix hsr))
      (show k < (scheduleSpec s).2.2.length by omega)
    have ha : instrAngle (scheduleSpec s) k = instrAngle (scheduleSpec r) k := by
      unfold instrAngle scheduleSpec
      rw [he]
    have ht : instrTime (scheduleSpec s) k = instrTime (scheduleSpec r) k := by
      unfold instrTime scheduleSpec
      rw [he]
    simp only [codeContext, ha, ht, codeContext_prefix h44 hκ hκ4 c hsr f k (by omega)]

theorem codeDriver_prefix (h44 : Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : BoundaryWord)
    {s r : Schedule} (hsr : s.1.IsPrefix r.1) (f : DistOn upperHalfPlaneOpens)
    {k : ℕ} (hk : k < (scheduleSpec s).2.2.length) :
    codeDriver h44 hκ hκ4 c (scheduleSpec s) k f =
      codeDriver h44 hκ hκ4 c (scheduleSpec r) k f := by
  have he := lookup_eq_of_prefix (scheduleProgram_prefix 0 (scheduleList_prefix hsr)) hk
  have ha : instrAngle (scheduleSpec s) k = instrAngle (scheduleSpec r) k := by
    unfold instrAngle scheduleSpec
    rw [he]
  simp only [codeDriver, ha, codeContext_prefix h44 hκ hκ4 c hsr f k hk.le]

def TimeOrdered (a : ℝ≥0) (l : List (ℝ × ℝ≥0)) : Prop :=
  l.Pairwise (fun p q => p.2 ≤ q.2) ∧ ∀ p ∈ l, a ≤ p.2

theorem timeOrdered_tail {a : ℝ≥0} {p : ℝ × ℝ≥0} {l : List (ℝ × ℝ≥0)}
    (hl : TimeOrdered a (p :: l)) : TimeOrdered p.2 l :=
  ⟨(List.pairwise_cons.1 hl.1).2, (List.pairwise_cons.1 hl.1).1⟩

theorem le_lastTime {a : ℝ≥0} {l : List (ℝ × ℝ≥0)} (hl : TimeOrdered a l) :
    a ≤ lastTime a l := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons p l ih => exact (hl.2 p List.mem_cons_self).trans (ih (timeOrdered_tail hl))

theorem joinedDriver_zero {Ω : Type*} (E : ℕ → Ω → Driver) (ω : Ω)
    (he : ∀ k, (E k ω).1 0 = 0) (j : ℕ) (a : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    joinedDriver E j a l ω 0 = 0 := by
  cases l with
  | nil => rfl
  | cons p l => exact catPath_zero (he j)

theorem joinedDriver_prefix {Ω : Type*} {E F : ℕ → Ω → Driver} (ω : Ω)
    (hF : ∀ k, (F k ω).1 0 = 0) (j : ℕ) (a : ℝ≥0)
    (l tail : List (ℝ × ℝ≥0)) (hl : TimeOrdered a l)
    (he : ∀ i, j ≤ i → i < j + l.length → E i ω = F i ω)
    {t : ℝ≥0} (ht : t ≤ lastTime a l - a) :
    joinedDriver E j a l ω t = joinedDriver F j a (l ++ tail) ω t := by
  induction l generalizing j a t with
  | nil =>
    have ht0 : t = 0 := by simpa only [lastTime, tsub_self, nonpos_iff_eq_zero] using ht
    rw [ht0, joinedDriver_zero F ω hF]
    rfl
  | cons p l ih =>
    change catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 l ω) t =
      catPath (F j ω).1 (p.2 - a) (joinedDriver F (j + 1) p.2 (l ++ tail) ω) t
    rw [he j le_rfl (by simp only [List.length_cons]; omega)]
    by_cases htp : t ≤ p.2 - a
    · simp only [catPath, htp, ↓reduceIte]
    · simp only [catPath, htp, ↓reduceIte]
      congr 1
      apply ih (j + 1) p.2 (timeOrdered_tail hl)
        (fun i hji hi => he i (by omega) (by simp only [List.length_cons]; omega))
      have hpa := hl.2 p List.mem_cons_self
      have hlast := le_lastTime (timeOrdered_tail hl)
      have htt : p.2 - a ≤ t := (lt_of_not_ge htp).le
      have ht' : (t : ℝ) ≤ (lastTime p.2 l : ℝ) - a := by
        have ht'' := NNReal.coe_le_coe.2 ht
        simpa only [lastTime, NNReal.coe_sub (hpa.trans hlast)] using ht''
      rw [← NNReal.coe_le_coe, NNReal.coe_sub htt, NNReal.coe_sub hpa, NNReal.coe_sub hlast]
      linarith only [ht']

end InteractingSLE.Sec5.Prop513Schedule
