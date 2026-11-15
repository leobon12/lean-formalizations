/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleInduction

/-!
# Availability through the terminal time, and field determination of prefixes

The source's closed availability predicate uses duration `≤` lifetime. In the
extreme-angle height regime every scheduled piece has infinite lifetime, so both
the closed and strict predicates hold simultaneously almost surely.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Prop513TreeExtract

/-- A finite schedule is defined through each requested terminal time. -/
def scheduleAvailableClosed {Ω : Type*} (E : Schedule → ℕ → Ω → Driver)
    (s : Schedule) (ω : Ω) : Prop :=
  ∀ j < (scheduleSpec s).2.2.length, instrTime (scheduleSpec s) j ≤ (E s j ω).2

theorem availableClosed_of_available {Ω : Type*} {E : Schedule → ℕ → Ω → Driver}
    {s : Schedule} {ω : Ω} (ha : scheduleAvailable E s ω) :
    scheduleAvailableClosed E s ω := fun j hj => (ha j hj).le

theorem available_of_top {Ω : Type*} {E : Schedule → ℕ → Ω → Driver}
    (s : Schedule) {ω : Ω}
    (he : ∀ j < (scheduleSpec s).2.2.length, (E s j ω).2 = ⊤) :
    scheduleAvailable E s ω := by
  intro j hj
  rw [he j hj]
  exact lt_top_iff_ne_top.2 (instrTime_finite s hj)

theorem joinedDriver_congr {Ω Ω' : Type*} {E : ℕ → Ω → Driver} {F : ℕ → Ω' → Driver}
    (ω : Ω) (ω' : Ω')
    (j : ℕ) (a : ℝ≥0) (l : List (ℝ × ℝ≥0))
    (he : ∀ i, j ≤ i → i < j + l.length → E i ω = F i ω') :
    joinedDriver E j a l ω = joinedDriver F j a l ω' := by
  induction l generalizing j a with
  | nil => rfl
  | cons p l ih =>
    change StripSideHeightProb.catPath (E j ω).1 (p.2 - a)
      (joinedDriver E (j + 1) p.2 l ω) = _
    rw [he j le_rfl (by simp only [List.length_cons]; omega)]
    rw [ih (j + 1) p.2 (fun i hji hi => he i (by omega)
      (by simp only [List.length_cons]; omega))]
    rfl

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  (c : BoundaryWord) (hc : ExtremeHeights κ c)
  (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
  {E : Schedule → ℕ → Ω → Driver}
  (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
  (hr : ∀ s j ω, IsRegularDriver (E s j ω))

include h44 hκ hκ4 c hc hh hE hr

/-- One conull event for all finite extreme schedules, including their endpoints. -/
theorem ae_all_schedules_available :
    ∀ᵐ ω ∂P, ∀ s, scheduleAvailable E s ω ∧ scheduleAvailableClosed E s ω := by
  have hD := fun s => ae_schedule_drivers h44 hκ hκ4 c hc hh s (hE s) (hr s)
  filter_upwards [ae_all_iff.2 hD] with ω hω s
  have ha := available_of_top s (fun j hj => (hω s j hj).1)
  exact ⟨ha, availableClosed_of_available ha⟩

theorem ae_strict_iff_closed :
    ∀ᵐ ω ∂P, ∀ s, scheduleAvailable E s ω ↔ scheduleAvailableClosed E s ω :=
  (ae_all_schedules_available h44 hκ hκ4 c hc hh hE hr).mono fun _ hω s =>
    ⟨fun _ => (hω s).2, fun _ => (hω s).1⟩

/-- The enumeration has an available root; no random search or positive-time
choice is needed in this regime. -/
theorem ae_nonempty_available :
    ∀ᵐ ω ∂P, ∃ n, scheduleAvailable E (scheduleAt n) ω :=
  (ae_all_schedules_available h44 hκ hκ4 c hc hh hE hr).mono fun _ hω =>
    ⟨0, (hω (scheduleAt 0)).1⟩

theorem prefixAvailabilityFieldStatement : PrefixAvailabilityFieldStatement P h E := by
  refine ⟨fun _ _ => true, fun _ => measurable_const, ?_⟩
  exact (ae_all_schedules_available h44 hκ hκ4 c hc hh hE hr).mono
    fun _ hω s => ⟨fun _ => (hω s).1, fun _ => rfl⟩

/-- The Borel prefix driver is obtained by finite concatenation of the
successive conditional-field codes. -/
theorem prefixFieldDrivers : PrefixFieldDrivers P (fun _ => univ) h E := by
  let D : Schedule → ℕ → DistOn upperHalfPlaneOpens → Driver :=
    fun s k => codeDriver h44 hκ hκ4 c (scheduleSpec s) k
  refine ⟨fun s => prefixDriver D s, fun s =>
    measurable_joinedDriver (fun k => measurable_codeDriver h44 hκ hκ4 c _ k) _ _ _, ?_⟩
  intro s
  filter_upwards [ae_schedule_drivers h44 hκ hκ4 c hc hh s (hE s) (hr s)] with ω hω _ t _
  have he : prefixDriver E s ω = prefixDriver D s (h ω) := by
    apply joinedDriver_congr
    intro j _ hj
    have hj' : j < (scheduleSpec s).2.2.length := by
      simpa only [scheduleSpec, length_scheduleProgram, zero_add] using hj
    exact (hω j hj').2
  exact congrFun he.symm t

end InteractingSLE.Sec5.Prop513Schedule
