/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TreeExtract
import InteractingSLE.Spec.Sec7.StripWallInputsReflDet

/-!
# Conditional words along finite extreme-angle schedules

The height envelope is preserved by every stopped piece at either extreme
angle. Its upper extreme satisfies (4.4); its lower extreme satisfies the
reflected (4.4). The context records the actual successive stop words and fields.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Schedule

open LQGMetric Restart Exist Exist.Staged Exist.StagedLaw
open Sec7 Sec7.StripWall Sec7.AdmCode QuantumZipper

abbrev Driver := (ℝ≥0 → ℝ) × ℝ≥0∞
abbrev Context := BoundaryWord × DistOn upperHalfPlaneOpens

/-- The conditional heights needed at the two extreme angles (R56). -/
def ExtremeHeights (κ : ℝ) (c : BoundaryWord) : Prop :=
  (∀ y : ℝ, y < 0 → y ∉ c.jumps → c.fn y ≤ -sleLambda κ + Real.pi / 2 * chiC κ) ∧
  ∀ y : ℝ, 0 < y → y ∉ c.jumps → sleLambda κ - Real.pi / 2 * chiC κ ≤ c.fn y

theorem extremeHeights_stopWord {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {c : BoundaryWord} (hc : ExtremeHeights κ c)
    (hθ : θ = -(Real.pi / 2) ∨ θ = Real.pi / 2) (r : RecData) :
    ExtremeHeights κ (stopWord κ (c, θ, r)) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  constructor
  · intro y hy _
    rcases stopWord_fn_of_neg hκ c θ r hy with he | ⟨x, hx, hxJ, he⟩
    · rw [he]
      rcases hθ with rfl | rfl <;> nlinarith only [hχ, Real.pi_pos]
    · rw [he]
      exact hc.1 x hx hxJ
  · intro y hy _
    rcases stopWord_fn_of_pos hκ c θ r hy with he | ⟨x, hx, hxJ, he⟩
    · rw [he]
      rcases hθ with rfl | rfl <;> nlinarith only [hχ, Real.pi_pos]
    · rw [he]
      exact hc.2 x hx hxJ

theorem cond44_upper {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    (hc : ExtremeHeights κ c) :
    Sec4.Cond44 κ (flowLineRhoL κ c.fn c.jumps 0 (Real.pi / 2))
      (flowLineRhoR κ c.fn c.jumps 0 (Real.pi / 2)) := by
  apply StripDet.cond44_flowLine_of_heights hκ c.isPiecewiseConstantBoundaryData
  · intro y hy hyJ
    linarith only [hc.1 y hy hyJ]
  · intro y hy hyJ
    linarith only [hc.2 y hy hyJ]

theorem cond44_lower {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord}
    (hc : ExtremeHeights κ c) :
    Sec4.Cond44 κ (flowLineRhoL κ (reflWord c).fn (reflWord c).jumps 0 (Real.pi / 2))
      (flowLineRhoR κ (reflWord c).fn (reflWord c).jumps 0 (Real.pi / 2)) := by
  apply StripDet.cond44_flowLine_of_heights hκ (reflWord c).isPiecewiseConstantBoundaryData
  · intro y hy hyJ
    have hyJ' : -y ∉ c.jumps := fun h => hyJ (mem_jumps_reflWord.2 h)
    rw [fn_reflWord hyJ']
    change -c.fn (-y) + _ ≤ _
    linarith only [hc.2 (-y) (neg_pos.2 hy) hyJ']
  · intro y hy hyJ
    have hyJ' : -y ∉ c.jumps := fun h => hyJ (mem_jumps_reflWord.2 h)
    rw [fn_reflWord hyJ']
    change _ ≤ -c.fn (-y) + _
    linarith only [hc.1 (-y) (neg_neg_of_pos hy) hyJ']

/-- Read the next word and field in the stopped piece's chart. -/
def advance (κ θ : ℝ) (t : ℝ≥0∞) (e : Driver) (c : Context) : Context :=
  (stopWord κ (c.1, θ, recOf t e), recField κ (recOf t e) c.2)

theorem measurable_advance {Ω : Type*} [MeasurableSpace Ω] (κ θ : ℝ) (t : ℝ≥0∞)
    {e : Ω → Driver} {c : Ω → Context} (he : Measurable e)
    (her : ∀ ω, IsRegularDriver (e ω)) (hc : Measurable c) :
    Measurable fun ω => advance κ θ t (e ω) (c ω) := by
  have hr : Measurable (fun ω => recOf t (e ω)) := measurable_recOf he her t
  have hw : Measurable fun ω => stopWord κ ((c ω).1, θ, recOf t (e ω)) :=
    Measurable.comp (g := stopWord κ)
      (f := fun ω => ((c ω).1, θ, recOf t (e ω))) (measurable_stopWord κ)
      ((measurable_fst.comp hc).prodMk (measurable_const.prodMk hr))
  have hf : Measurable fun ω => recField κ (recOf t (e ω)) (c ω).2 :=
    Measurable.comp (g := fun p : RecData × DistOn upperHalfPlaneOpens =>
      recField κ p.1 p.2) (f := fun ω => (recOf t (e ω), (c ω).2))
      (measurable_recField κ) (hr.prodMk (measurable_snd.comp hc))
  change Measurable fun ω =>
    (stopWord κ ((c ω).1, θ, recOf t (e ω)), recField κ (recOf t (e ω)) (c ω).2)
  exact hw.prodMk hf

/-- The context before instruction `k`, using the actual ordinary pieces. -/
def context (κ : ℝ) (c : BoundaryWord) (spec : ExplSpec) {Ω : Type*}
    (h : Ω → DistOn upperHalfPlaneOpens) (E : ℕ → Ω → Driver) : ℕ → Ω → Context
  | 0, ω => (c, h ω)
  | k + 1, ω => advance κ (instrAngle spec k) (instrTime spec k) (E k ω)
      (context κ c spec h E k ω)

theorem measurable_context {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) (c : BoundaryWord)
    (spec : ExplSpec) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {E : ℕ → Ω → Driver} (hE : ∀ k, Measurable (E k))
    (hr : ∀ k ω, IsRegularDriver (E k ω)) : ∀ k, Measurable (context κ c spec h E k)
  | 0 => measurable_const.prodMk hh
  | k + 1 => measurable_advance _ _ _ (hE k) (hr k)
      (measurable_context κ c spec hh hE hr k)

end InteractingSLE.Sec5.Prop513Schedule
