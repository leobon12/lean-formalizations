/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleTrace

/-!
# Agreement of the actual staged prefixes

Programs sharing a syntactic prefix have the same conditional driver codes.
Their actual concatenated drivers therefore agree through the common terminal
time. Uniqueness of continuous generating traces includes that terminal point.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Prop513TreeExtract

theorem prefixEndpointCompatibility (h44 : Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
    (hr : ∀ s j ω, IsRegularDriver (E s j ω)) : PrefixEndpointCompatibility P E := by
  have hD := fun s => ae_schedule_drivers h44 hκ hκ4 c hc hh s (hE s) (hr s)
  filter_upwards [ae_all_iff.2 hD] with ω hd n m _ _ η η' hη hη'
  let s := scheduleAt n
  let r := scheduleAt (descendantIndex n m)
  have hsr : s.1.IsPrefix r.1 := schedule_descendant_prefix n m
  have hprog := scheduleProgram_prefix 0 (scheduleList_prefix hsr)
  have hlen : (scheduleSpec s).2.2.length ≤ (scheduleSpec r).2.2.length := hprog.length_le
  have he : ∀ j, 0 ≤ j → j < 0 + (scheduleList s).length → E s j ω = E r j ω := by
    intro j _ hj
    have hj' : j < (scheduleSpec s).2.2.length := by
      simpa only [scheduleSpec, length_scheduleProgram, zero_add] using hj
    exact (hd s j hj').2.trans ((codeDriver_prefix h44 hκ hκ4 c hsr (h ω) hj').trans
      (hd r j (hj'.trans_le hlen)).2.symm)
  obtain ⟨tail, htail⟩ := scheduleList_prefix hsr
  have heq : ∀ t : ℝ≥0, t ≤ terminal s → prefixDriver E s ω t = prefixDriver E r ω t := by
    intro t ht
    have ht' : t ≤ lastTime 0 (scheduleList s) - 0 := by
      simpa only [← terminal_eq_lastTime, tsub_zero] using ht
    have hp := joinedDriver_prefix (E := E s) (F := E r) ω (fun j => (hr r j ω).2.1)
      0 0 (scheduleList s) tail (timeOrdered_scheduleList s) he ht'
    rw [htail] at hp
    exact hp
  have hcont := joinedDriver_continuous (E s) ω 0 0 (scheduleList s) (fun j _ hj => by
    have hj' : j < (scheduleSpec s).2.2.length := by
      simpa only [scheduleSpec, length_scheduleProgram, zero_add] using hj
    exact ⟨Sec7.StripWall.continuous_of_isRegularDriver (hr s j ω) (hd s j hj').1,
      (hr s j ω).2.1⟩)
  have hchild : IsGeneratingTrace (prefixDriver E s ω) (terminal s) η' := by
    apply Sec7.IsGeneratingTrace.congr_lt
      (hη'.mono_horizon (ENNReal.coe_le_coe.2 (terminal_descendant_le n m)))
    intro t ht
    exact heq t (ENNReal.coe_lt_coe.1 ht).le
  exact hchild.eq_of_le hη hcont.1.continuousOn hcont.2 le_rfl

end InteractingSLE.Sec5.Prop513Schedule
