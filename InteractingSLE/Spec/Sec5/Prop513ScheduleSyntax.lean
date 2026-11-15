/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleData

/-!
# Finite ordinary programs launch every piece before an infinite lifetime

These deterministic lemmas use the frozen staged construction and its actual
own-capacity durations. No probability or field-determination theorem is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Schedule

open Exist.Staged Exist.StagedLaw Prop513TreeExtract

theorem length_scheduleProgram (a : ℝ≥0) (l : List (ℝ × ℝ≥0)) :
    (scheduleProgram a l).length = l.length := by
  induction l generalizing a with
  | nil => rfl
  | cons p l ih => exact congrArg Nat.succ (ih p.2)

theorem lookup_scheduleProgram (a : ℝ≥0) (l : List (ℝ × ℝ≥0)) {k : ℕ}
    (hk : k < l.length) : ∃ p ∈ l, ∃ t : ℝ≥0,
      (scheduleProgram a l)[k]? = some (Sum.inl (p.1, (t : ℝ≥0∞))) := by
  induction l generalizing a k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons p l ih =>
    cases k with
    | zero => exact ⟨p, List.mem_cons_self, p.2 - a, rfl⟩
    | succ k =>
      obtain ⟨p', hp', t, ht⟩ := ih p.2 (Nat.lt_of_succ_lt_succ hk)
      exact ⟨p', List.mem_cons_of_mem p hp', t, ht⟩

theorem instrTime_finite (s : Schedule) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length) : instrTime (scheduleSpec s) k ≠ ⊤ := by
  have hk' : k < (scheduleList s).length := by
    simpa only [scheduleSpec, length_scheduleProgram] using hk
  obtain ⟨p, _, t, ht⟩ := lookup_scheduleProgram 0 (scheduleList s) hk'
  simp only [instrTime, scheduleSpec, ht]
  exact ENNReal.coe_ne_top

theorem instrAngle_extreme (s : Schedule) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length) :
    instrAngle (scheduleSpec s) k = -(Real.pi / 2) ∨
      instrAngle (scheduleSpec s) k = Real.pi / 2 := by
  have hk' : k < (scheduleList s).length := by
    simpa only [scheduleSpec, length_scheduleProgram] using hk
  obtain ⟨p, hp, t, ht⟩ := lookup_scheduleProgram 0 (scheduleList s) hk'
  obtain ⟨⟨b, q⟩, _, rfl⟩ := List.mem_map.1 hp
  cases b <;> simp only [instrAngle, scheduleSpec, ht, Bool.false_eq_true,
    ↓reduceIte, or_true, true_or]

def Active (st : ExplState) : Prop :=
  st.2.2.2.2.2.1 = .inl () ∨ st.2.2.2.2.2.1 = .inr (.inl ())

theorem flowStep_of_active {κ : ℝ} {b : ℝ → ℝ} {s : ExplState}
    (hs : Active s) (gw2 : Bool) (k : ℕ) (e : Driver) (θ : ℝ) (t : ℝ≥0∞) :
    ExplState.flowStep κ b gw2 s k e θ t = ExplState.launch s k e θ t := by
  rcases hs with hs | hs <;> simp only [ExplState.flowStep, hs]

theorem active_launch (s : ExplState) (k : ℕ) (e : Driver) (θ : ℝ) (t : ℝ≥0∞)
    (ht : t ≠ ⊤) (he : t < e.2) : Active (ExplState.launch s k e θ t) := by
  right
  simp only [ExplState.launch, min_eq_left he.le, ht, ↓reduceIte, he]

theorem run_succ_of_active {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (s : Schedule) (D : ℕ → Driver) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length)
    (ha : Active (ExplState.run κ b J (scheduleSpec s) D k)) :
    ExplState.run κ b J (scheduleSpec s) D (k + 1) =
      ExplState.launch (ExplState.run κ b J (scheduleSpec s) D k) k (D k)
        (instrAngle (scheduleSpec s) k) (instrTime (scheduleSpec s) k) := by
  have hk' : k < (scheduleList s).length := by
    simpa only [scheduleSpec, length_scheduleProgram] using hk
  obtain ⟨p, _, t, ht⟩ := lookup_scheduleProgram 0 (scheduleList s) hk'
  rw [run_succ]
  simp only [scheduleSpec, ht, ExplState.step, instrAngle, instrTime]
  exact flowStep_of_active ha _ _ _ _ _

theorem active_run {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} (s : Schedule)
    (D : ℕ → Driver) : ∀ k, k ≤ (scheduleSpec s).2.2.length →
      (∀ j < k, (D j).2 = ⊤) → Active (ExplState.run κ b J (scheduleSpec s) D k)
  | 0, _, _ => Or.inl rfl
  | k + 1, hk, hD => by
    have ha := active_run (κ := κ) (b := b) (J := J) s D k (by omega)
      (fun j hj => hD j (by omega))
    rw [run_succ_of_active s D (by omega) ha]
    exact active_launch _ _ _ _ _ (instrTime_finite s (by omega))
      (by rw [hD k (by omega)]; exact lt_top_iff_ne_top.2 (instrTime_finite s (by omega)))

theorem launch_of_previous_top {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    (s : Schedule) (D : ℕ → Driver) {k : ℕ} (hk : k < (scheduleSpec s).2.2.length)
    (hD : ∀ j < k, (D j).2 = ⊤) :
    (ExplState.run κ b J (scheduleSpec s) D (k + 1)).2.2.2.1 k ≠ none := by
  rw [run_succ_of_active s D hk (active_run s D k hk.le hD), launches_launch]
  simp only [Function.update_self, ne_eq, reduceCtorEq, not_false_eq_true]

theorem extremeHeights_context {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {c : Restart.BoundaryWord} (hc : ExtremeHeights κ c) (s : Schedule)
    {Ω : Type*} (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (E : ℕ → Ω → Driver) :
    ∀ k, k ≤ (scheduleSpec s).2.2.length → ∀ ω,
      ExtremeHeights κ (context κ c (scheduleSpec s) h E k ω).1
  | 0, _, _ => hc
  | k + 1, hk, ω => extremeHeights_stopWord hκ hκ4
      (extremeHeights_context hκ hκ4 hc s h E k (by omega) ω)
      (instrAngle_extreme s (by omega)) _

end InteractingSLE.Sec5.Prop513Schedule
