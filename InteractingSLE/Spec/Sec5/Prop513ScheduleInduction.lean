/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleLaw

/-!
# R48-safe induction over a finite extreme-angle schedule

Every launched ordinary driver has infinite lifetime and is the Borel code
obtained by updating the actual conditional word and chart field. The induction
simultaneously supplies the marked Gaussian witness for the next instruction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.AdmCode Prop513TreeExtract

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

theorem context_eq_codeContext (c : BoundaryWord) (spec : ExplSpec) {Ω : Type*}
    (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → Driver) (ω : Ω) :
    ∀ k, (∀ j < k, E j ω = codeDriver h44 hκ hκ4 c spec j (h ω)) →
      context κ c spec h E k ω = codeContext h44 hκ hκ4 c spec k (h ω)
  | 0, _ => rfl
  | k + 1, he => by
    rw [context, he k (Nat.lt_succ_self k),
      context_eq_codeContext c spec h E ω k (fun j hj => he j (by omega))]
    rfl

theorem finite_schedule_induction {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule)
    {E : ℕ → Ω → Driver} (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E)
    (hr : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ k, k ≤ (scheduleSpec s).2.2.length →
      ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
        IsStageWitness κ c.fn c.jumps P h (scheduleSpec s) E k β Y ∧
        (∀ᵐ ω ∂P, (β ω, Y ω) = codeContext h44 hκ hκ4 c (scheduleSpec s) k (h ω) ∧
          ∀ j < k, (E j ω).2 = ⊤ ∧
            E j ω = codeDriver h44 hκ hκ4 c (scheduleSpec s) j (h ω)) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => c, h, stageWitness_zero s c hh, ?_⟩
    exact Eventually.of_forall fun _ => ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ k ih =>
    intro hk
    obtain ⟨β, Y, hw, he⟩ := ih (by omega)
    have hk' : k < (scheduleSpec s).2.2.length := by omega
    have hβH : ∀ᵐ ω ∂P, ExtremeHeights κ (β ω) := by
      filter_upwards [he] with ω ⟨hctx, hprev⟩
      have ht := extremeHeights_context hκ hκ4 hc s h E k (by omega) ω
      rw [context_eq_codeContext h44 hκ hκ4 c (scheduleSpec s) h E ω k
        (fun j hj => (hprev j hj).2), ← hctx] at ht
      exact ht
    have hstage := ae_stage_eq_of_witness h44 hκ hκ4 c.isPiecewiseConstantBoundaryData
      hh s hE hr hk' hw hβH
    have hstep : ∀ᵐ ω ∂P, (E k ω).2 = ⊤ ∧
        E k ω = codeDriver h44 hκ hκ4 c (scheduleSpec s) k (h ω) := by
      filter_upwards [he, hstage] with ω ⟨hctx, hprev⟩ hs
      obtain ⟨htop, hdriver⟩ := hs (launch_of_previous_top s _ hk'
        (fun j hj => (hprev j hj).1))
      exact ⟨htop, hdriver.trans (congrArg
        (stageDriver h44 hκ hκ4 (instrAngle (scheduleSpec s) k)) hctx)⟩
    have hTop : ∀ᵐ ω ∂P, ∀ j < k + 1, (E j ω).2 = ⊤ := by
      filter_upwards [he, hstep] with ω hprev hs j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact (hprev.2 j hj).1
      · exact hs.1
    let R := fun ω => pastMap κ c.fn c.jumps (scheduleSpec s) E (k + 1) ω (Fin.last k)
    refine ⟨fun ω => stopWord κ (β ω, instrAngle (scheduleSpec s) k, R ω),
      fun ω => recField κ (R ω) (Y ω),
      stageWitness_succ hκ c.isPiecewiseConstantBoundaryData hh s hE hr hk' hTop hw, ?_⟩
    filter_upwards [he, hstep] with ω ⟨hctx, hprev⟩ hs
    have hR : R ω = recOf (instrTime (scheduleSpec s) k) (E k ω) :=
      pastMap_last_of_launch (launch_of_previous_top s _ hk' (fun j hj => (hprev j hj).1))
    refine ⟨?_, fun j hj => ?_⟩
    · rw [hR]
      change advance κ (instrAngle (scheduleSpec s) k) (instrTime (scheduleSpec s) k)
        (E k ω) (β ω, Y ω) = _
      rw [hs.2, hctx]
      rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hprev j hj
      · exact hs

/-- All ordinary pieces of the schedule are Borel functions of the original field. -/
theorem ae_schedule_drivers {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (c : BoundaryWord) (hc : ExtremeHeights κ c)
    (hh : IsGFFWithBoundaryData P h c.fn c.jumps) (s : Schedule)
    {E : ℕ → Ω → Driver} (hE : IsStagedHistory κ c.fn c.jumps P h (scheduleSpec s) E)
    (hr : ∀ j ω, IsRegularDriver (E j ω)) :
    ∀ᵐ ω ∂P, ∀ j < (scheduleSpec s).2.2.length, (E j ω).2 = ⊤ ∧
      E j ω = codeDriver h44 hκ hκ4 c (scheduleSpec s) j (h ω) := by
  obtain ⟨_, _, _, he⟩ := finite_schedule_induction h44 hκ hκ4 c hc hh s hE hr
    (scheduleSpec s).2.2.length le_rfl
  exact he.mono fun _ hω => hω.2

end InteractingSLE.Sec5.Prop513Schedule
