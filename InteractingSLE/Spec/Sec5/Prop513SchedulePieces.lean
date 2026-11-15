/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleInduction
import InteractingSLE.Spec.Sec7.StripWallVersionPiece

/-!
# One-piece regularity at every finite schedule stage

The Borel good-path event permits the conditional-kernel transfer required by
R51. It supplies actual full generating traces, not just a nonmeasurable
kernel-almost-sure assertion of continuity.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Sec7.StripWall Prop513TreeExtract QuantumZipper
open Sec4

theorem admissible_extreme {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {c : BoundaryWord} (hc : ExtremeHeights κ c)
    (hθ : θ = -(Real.pi / 2) ∨ θ = Real.pi / 2) :
    HasAdmissiblePartialSums κ (flowLineRhoL κ c.fn c.jumps 0 θ)
      (flowLineRhoR κ c.fn c.jumps 0 θ) (flowLineXL c.fn c.jumps 0)
      (flowLineXR c.fn c.jumps 0) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  apply hasAdmissiblePartialSums_flowLine_of_heights hκ c.isPiecewiseConstantBoundaryData
  · intro y hy hyJ
    have h := hc.1 y hy hyJ
    rcases hθ with rfl | rfl <;> nlinarith only [h, hχ, Real.pi_pos]
  · intro y hy hyJ
    have h := hc.2 y hy hyJ
    rcases hθ with rfl | rfl <;> nlinarith only [h, hχ, Real.pi_pos]

/-- Every actual stage belongs to the Borel event of drivers with a simple
transient generating trace. -/
theorem ae_schedule_goodPath (h44 : Theorem12ParamCond44Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule)
    {E : ℕ → Ω → Driver} (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E)
    (hr : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, ∀ k < (scheduleSpec s).2.2.length, E k ω ∈ goodPathSet := by
  have hD := ae_schedule_drivers h44 hκ hκ4 c hc hh s hE hr
  apply ae_all_iff.2
  intro k
  by_cases hk : k < (scheduleSpec s).2.2.length
  · obtain ⟨β, Y, hw, he⟩ := finite_schedule_induction h44 hκ hκ4 c hc hh s hE hr k hk.le
    have hadm : ∀ᵐ ω ∂P,
        (ExplState.run κ c.fn c.jumps (scheduleSpec s) (fun j => E j ω)
          (k + 1)).2.2.2.1 k ≠ none →
        HasAdmissiblePartialSums κ
          (flowLineRhoL κ (β ω).fn (β ω).jumps 0 (instrAngle (scheduleSpec s) k))
          (flowLineRhoR κ (β ω).fn (β ω).jumps 0 (instrAngle (scheduleSpec s) k))
          (flowLineXL (β ω).fn (β ω).jumps 0) (flowLineXR (β ω).fn (β ω).jumps 0) := by
      filter_upwards [he] with ω ⟨hctx, hprev⟩ _
      have hhgt := extremeHeights_context hκ hκ4 hc s h E k hk.le ω
      rw [context_eq_codeContext h44 hκ hκ4 c (scheduleSpec s) h E ω k
        (fun j hj => (hprev j hj).2), ← hctx] at hhgt
      exact admissible_extreme hκ hκ4 hhgt (instrAngle_extreme s hk)
    have hg := ae_goodPath_stage hκ hκ4 c.isPiecewiseConstantBoundaryData hh hE hr k
      hw.2.2.1 hw.2.2.2 hadm
    filter_upwards [hg, hD] with ω hgω hdω _
    exact hgω (launch_of_previous_top s _ hk (fun j hj => (hdω j (hj.trans hk)).1))
  · exact Eventually.of_forall fun _ h => absurd h hk

end InteractingSLE.Sec5.Prop513Schedule
