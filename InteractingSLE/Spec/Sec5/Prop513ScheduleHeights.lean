/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleExtract
import InteractingSLE.Spec.Sec4.Prob41Charts

/-!
# The source strip heights give the extreme-angle envelope in chart Q

The target chart is `(exp (π z) - 1) / (exp (π z) + exp (π x₀))`.
Its upper-side derivative arguments are `π` and `-π`. The source's standing
Figure 5.1/5.5 bounds consequently give exactly the envelope used by the induction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Schedule

open Sec4 QuantumZipper Restart

theorem stripQHData_add_const (κ q d : ℝ) (bL bU : ℝ → ℝ) (y : ℝ) :
    stripQHData κ q (fun x => bL x + d) (fun x => bU x + d) y =
      stripQHData κ q bL bU y + d := by
  unfold stripQHData
  split_ifs <;> ring

theorem stripQ_extreme_bounds {κ q : ℝ} (hq : 0 < q) {bL bU : ℝ → ℝ}
    {JL JU : Finset ℝ}
    (hL : ∀ x, x < 0 → x ∉ JL → bL x ≤ -sleLambda κ + π / 2 * chiC κ)
    (hR : ∀ x, 0 < x → x ∉ JL → sleLambda κ - π / 2 * chiC κ ≤ bL x)
    (hU : ∀ x, x ∉ JU → Real.exp (π * x) < q → bU x ≤ -sleLambda κ - π / 2 * chiC κ)
    (hV : ∀ x, x ∉ JU → q < Real.exp (π * x) → sleLambda κ + π / 2 * chiC κ ≤ bU x) :
    (∀ y, y < 0 → y ∉ stripQHJumps q JL JU →
      stripQHData κ q bL bU y ≤ -sleLambda κ + π / 2 * chiC κ) ∧
    ∀ y, 0 < y → y ∉ stripQHJumps q JL JU →
      sleLambda κ - π / 2 * chiC κ ≤ stripQHData κ q bL bU y := by
  constructor
  · intro y hy hyJ
    have hh := stripQHData_le_of_neg (k := κ) hq
      (bL := fun x => bL x + π / 2 * chiC κ)
      (bU := fun x => bU x + π / 2 * chiC κ)
      (fun x hx hxq => by linarith only [hU x hx hxq])
      (fun x hx hxJ => by linarith only [hL x hx hxJ]) hy hyJ
    rw [stripQHData_add_const] at hh
    linarith only [hh]
  · intro y hy hyJ
    have hh := le_stripQHData_of_pos (k := κ) hq
      (bL := fun x => bL x + (-(π / 2 * chiC κ)))
      (bU := fun x => bU x + (-(π / 2 * chiC κ)))
      (fun x hx hxq => by linarith only [hV x hx hxq])
      (fun x hx hxJ => by linarith only [hR x hx hxJ]) hy hyJ
    rw [stripQHData_add_const] at hh
    linarith only [hh]

/-- R56 for the source's chosen heights, in the target-normalized chart Q. -/
theorem exists_extremeWord_fig51 {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    (hb : IsFig51Bounds κ a b a' b') :
    ∃ c : BoundaryWord,
      c.jumps = stripQHJumps (Real.exp (π * x₀)) {0} {x₀} ∧
      (∀ y ∉ c.jumps, c.fn y =
        stripQHData κ (Real.exp (π * x₀)) (fig51Lower a b) (fig51Upper x₀ a' b') y) ∧
      ExtremeHeights κ c := by
  have hq : 0 < Real.exp (π * x₀) := Real.exp_pos _
  obtain ⟨c, hcJ, hc⟩ := BoundaryWord.exists_fn_eq
    (isPiecewiseConstantBoundaryData_stripQHData (k := κ) hq
      (isPiecewiseConstantBoundaryData_fig51Lower a b)
      (isPiecewiseConstantBoundaryData_fig51Upper x₀ a' b'))
  have hlam := sleLambda_sixteen_div_eq_sub hκ
  have hbounds := stripQ_extreme_bounds (κ := κ) hq
    (JL := {0}) (JU := {x₀})
    (bL := fig51Lower a b) (bU := fig51Upper x₀ a' b')
    (fun x hx _ => by rw [fig51Lower_of_neg hx]; linarith only [hb.1, hlam])
    (fun x hx _ => by rw [fig51Lower_of_pos hx]; linarith only [hb.2.1, hlam])
    (fun x _ hx => by
      have hxx : x < x₀ := (mul_lt_mul_iff_right₀ Real.pi_pos).1 (Real.exp_lt_exp.1 hx)
      rw [fig51Upper_of_lt hxx]
      linarith only [hb.2.2.1, hlam])
    (fun x _ hx => by
      have hxx : x₀ < x := (mul_lt_mul_iff_right₀ Real.pi_pos).1 (Real.exp_lt_exp.1 hx)
      rw [fig51Upper_of_gt hxx]
      linarith only [hb.2.2.2, hlam])
  refine ⟨c, hcJ, fun y hy => hc y (by rwa [← hcJ]), ?_⟩
  constructor
  · intro y hy hyJ
    rw [hc y (by rwa [← hcJ])]
    exact hbounds.1 y hy (by rwa [← hcJ])
  · intro y hy hyJ
    rw [hc y (by rwa [← hcJ])]
    exact hbounds.2 y hy (by rwa [← hcJ])

end InteractingSLE.Sec5.Prop513Schedule
