/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleCompatibility

/-!
# The measurable extreme-angle tree from regular staged histories

All finite-prefix inputs of the earlier extraction are now consequences of the
R48-safe finite-schedule induction, in the R56 height-envelope regime. The paths
are measurable for the original field sigma algebra and have exact common nodes.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Prop513TreeExtract

/-- Countably many field-measurable continuous prefixes with exact common nodes.
Every actual generating trace agrees with its enumerated path through the finite
terminal time, simultaneously for all schedules. -/
theorem exists_measurable_extreme_tree (h44 : Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps)
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) (E s))
    (hr : ∀ s j ω, IsRegularDriver (E s j ω)) (hh𝒢 : Measurable[𝒢] h) :
    ∃ ξ : ℕ → Ω → ℝ → ℂ,
      (∀ n t, Measurable[𝒢] fun ω => ξ n ω t) ∧
      (∀ n ω, Continuous (ξ n ω)) ∧
      (∀ n m ω, ξ (descendantIndex n m) ω (terminal (scheduleAt n)) =
        extremeAngleTreeNode ξ (fun n => terminal (scheduleAt n)) n ω) ∧
      ∀ᵐ ω ∂P, ∀ n, ∀ η : ℝ≥0 → ℂ,
        IsGeneratingTrace (prefixDriver E (scheduleAt n) ω) (terminal (scheduleAt n)) η →
        EqOn (ξ n ω) (fun t : ℝ => η t.toNNReal) (Icc 0 (terminal (scheduleAt n) : ℝ)) := by
  have hR := prefixTraceRegularity h44 hκ hκ4 c hc hh hE hr
  have hF := prefixFieldDrivers h44 hκ hκ4 c hc hh hE hr
  obtain ⟨ξ, hξm, hξc, hξe⟩ := @exists_available_prefix_paths Ω mΩ P 𝒢 h hh𝒢
    E (fun _ => univ) (fun _ => MeasurableSet.univ) hR hF
  have hRe : PrefixTraceRegularity P (fun s => {ω | scheduleAvailable E s ω}) E := by
    intro s
    exact (hR s).mono fun ω hω _ => hω (mem_univ _)
  have hξa : ∀ᵐ ω ∂P, ∀ s, scheduleAvailable E s ω → ∀ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (prefixDriver E s ω) (terminal s) η →
        EqOn (ξ s ω) (fun t : ℝ => η t.toNNReal) (Icc 0 (terminal s : ℝ)) :=
    hξe.mono fun _ he s _ => he s (mem_univ _)
  have hAgree := ae_available_prefix_agreement hRe
    (prefixEndpointCompatibility h44 hκ hκ4 c hc hh hE hr) hξa
  have hAvail := ae_all_schedules_available h44 hκ hκ4 c hc hh hE hr
  have hRoot : ∀ᵐ ω ∂P, ∀ n m,
      ξ (scheduleAt (descendantIndex n m)) ω (terminal (scheduleAt n)) =
        ξ (scheduleAt n) ω (terminal (scheduleAt n)) := by
    filter_upwards [hAgree, hAvail] with ω ha hv n m
    exact ha n m (hv _).1 (hv _).1
  let τ : ℕ → ℝ := fun n => terminal (scheduleAt n)
  obtain ⟨ξ', hm, hcont, hroot, he⟩ := @exists_tree_version Ω mΩ P 𝒢
    (fun n => ξ (scheduleAt n)) (fun n t => hξm _ t) τ descendantIndex
    (fun n => by exact_mod_cast terminal_pos (scheduleAt n))
    (fun n m => by exact_mod_cast terminal_descendant_le n m)
    (Eventually.of_forall fun ω n => (hξc _ ω).continuousOn) hRoot
  refine ⟨ξ', hm, hcont, hroot, ?_⟩
  filter_upwards [he, hξe] with ω heω hξω n η hη t ht
  exact (heω n ht).trans (hξω (scheduleAt n) (mem_univ _) η hη ht)

end InteractingSLE.Sec5.Prop513Schedule
