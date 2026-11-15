/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleSyntax

/-!
# The Borel recursion for the extreme-angle schedule drivers

The recursion alternates the direct and reflected Section 4.2 determination
maps as needed. Its contexts are the successive actual stop words and fields,
not a parametric Theorem 1.2/1.3 construction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.StripWall Sec7.AdmCode Prop513TreeExtract

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)

/-- Use reflection for the lower extreme, returning to the original coordinates. -/
def stageDriver (θ : ℝ) (c : Context) : Driver :=
  if θ < 0 then negDrv (admDrv h44 hκ hκ4 (-θ) (reflWord c.1, FlowReflect.reflField c.2))
  else admDrv h44 hκ hκ4 θ c

theorem measurable_stageDriver (θ : ℝ) : Measurable (stageDriver h44 hκ hκ4 θ) := by
  unfold stageDriver
  split_ifs
  · exact measurable_negDrv.comp ((measurable_admDrv h44 hκ hκ4 (-θ)).comp
      ((measurable_reflWord.comp measurable_fst).prodMk
        (FlowReflect.measurable_reflField.comp measurable_snd)))
  · exact measurable_admDrv h44 hκ hκ4 θ

theorem stageDriver_regular (θ : ℝ) (c : Context) :
    IsRegularDriver (stageDriver h44 hκ hκ4 θ c) := by
  unfold stageDriver
  split_ifs
  · exact isRegularDriver_negDrv (admDrv_regular h44 hκ hκ4 _ _)
  · exact admDrv_regular h44 hκ hκ4 _ _

/-- The canonical context, before instruction `k`, as a Borel function of the field. -/
def codeContext (c : BoundaryWord) (spec : ExplSpec) :
    ℕ → DistOn upperHalfPlaneOpens → Context
  | 0, f => (c, f)
  | k + 1, f => advance κ (instrAngle spec k) (instrTime spec k)
      (stageDriver h44 hκ hκ4 (instrAngle spec k) (codeContext c spec k f))
      (codeContext c spec k f)

def codeDriver (c : BoundaryWord) (spec : ExplSpec) (k : ℕ)
    (f : DistOn upperHalfPlaneOpens) : Driver :=
  stageDriver h44 hκ hκ4 (instrAngle spec k) (codeContext h44 hκ hκ4 c spec k f)

theorem measurable_codeContext (c : BoundaryWord) (spec : ExplSpec) :
    ∀ k, Measurable (codeContext h44 hκ hκ4 c spec k)
  | 0 => measurable_const.prodMk measurable_id
  | k + 1 => by
    have hc := measurable_codeContext c spec k
    apply measurable_advance _ _ _
    · exact (measurable_stageDriver h44 hκ hκ4 _).comp hc
    · exact fun _ => stageDriver_regular h44 hκ hκ4 _ _
    · exact hc

theorem measurable_codeDriver (c : BoundaryWord) (spec : ExplSpec) (k : ℕ) :
    Measurable (codeDriver h44 hκ hκ4 c spec k) :=
  (measurable_stageDriver h44 hκ hκ4 _).comp
    (measurable_codeContext h44 hκ hκ4 c spec k)

theorem codeDriver_regular (c : BoundaryWord) (spec : ExplSpec) (k : ℕ)
    (f : DistOn upperHalfPlaneOpens) :
    IsRegularDriver (codeDriver h44 hκ hκ4 c spec k f) :=
  stageDriver_regular h44 hκ hκ4 _ _

/-- The direct/reflected conditional-stage determination, in original coordinates. -/
theorem ae_stage_eq_of_witness {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {E : ℕ → Ω → Driver}
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (s : Schedule) (hE : IsStagedHistory κ b J P h (scheduleSpec s) E)
    (hr : ∀ j ω, IsRegularDriver (E j ω)) {k : ℕ}
    (hk : k < (scheduleSpec s).2.2.length)
    {β : Ω → BoundaryWord} {Y : Ω → DistOn upperHalfPlaneOpens}
    (hw : IsStageWitness κ b J P h (scheduleSpec s) E k β Y)
    (hc : ∀ᵐ ω ∂P, ExtremeHeights κ (β ω)) :
    ∀ᵐ ω ∂P,
      (ExplState.run κ b J (scheduleSpec s) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
      (E k ω).2 = ⊤ ∧ E k ω = stageDriver h44 hκ hκ4 (instrAngle (scheduleSpec s) k)
        (β ω, Y ω) := by
  rcases instrAngle_extreme s hk with hθ | hθ
  · have h44w := hc.mono fun ω hcω => cond44_lower hκ hcω
    have h44w' : ∀ᵐ ω ∂P,
        (ExplState.run κ b J (scheduleSpec s) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        Sec4.Cond44 κ
          (flowLineRhoL κ (reflWord (β ω)).fn (reflWord (β ω)).jumps 0
            (-instrAngle (scheduleSpec s) k))
          (flowLineRhoR κ (reflWord (β ω)).fn (reflWord (β ω)).jumps 0
            (-instrAngle (scheduleSpec s) k)) := by
      filter_upwards [h44w] with ω hω _
      simpa only [hθ, neg_neg] using hω
    filter_upwards [ae_stageDrv_eq_refl h44 hκ hκ4 hb hh hE hr k
      hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 h44w'] with ω hω hl
    obtain ⟨htop, hζ, he⟩ := hω hl
    refine ⟨htop, ?_⟩
    have hn : instrAngle (scheduleSpec s) k < 0 := by rw [hθ]; linarith [Real.pi_pos]
    apply Prod.ext
    · funext t
      simp only [stageDriver, hn, ↓reduceIte, negDrv]
      rw [he t (by rw [htop]; exact ENNReal.coe_lt_top), neg_neg]
    · simpa only [stageDriver, hn, ↓reduceIte, negDrv] using hζ.symm
  · have h44w := hc.mono fun ω hcω => cond44_upper hκ hcω
    have h44w' : ∀ᵐ ω ∂P,
        (ExplState.run κ b J (scheduleSpec s) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none →
        Sec4.Cond44 κ (flowLineRhoL κ (β ω).fn (β ω).jumps 0
          (instrAngle (scheduleSpec s) k)) (flowLineRhoR κ (β ω).fn (β ω).jumps 0
          (instrAngle (scheduleSpec s) k)) := by
      filter_upwards [h44w] with ω hω _
      simpa only [hθ] using hω
    filter_upwards [StripDet.ae_stageDrv_eq h44 hκ hκ4 hb hh hE hr k
      hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 h44w'] with ω hω hl
    obtain ⟨htop, hζ, he⟩ := hω hl
    refine ⟨htop, ?_⟩
    have hn : ¬instrAngle (scheduleSpec s) k < 0 := by rw [hθ]; linarith [Real.pi_pos]
    simp only [stageDriver, hn, ↓reduceIte]
    exact Prod.ext (funext fun t => (he t (by rw [htop]; exact ENNReal.coe_lt_top)).symm)
      hζ.symm

end InteractingSLE.Sec5.Prop513Schedule
