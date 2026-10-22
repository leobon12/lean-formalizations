import HigherDimLQGMetric.Freq.Iterate
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Card
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Counting powers of 64 in a logarithmic window

The integer exponents in `[ε²R, εR]` form an interval between the ceiling and
floor of its logarithmic endpoints.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set

private theorem s4c_int_interval_count {x y : ℝ} (hxy : x + 1 < y) :
    y - x - 1 ≤ ((Icc (⌈x⌉ : ℤ) ⌊y⌋).ncard : ℝ) := by
  have hc : (⌈x⌉ : ℤ) ≤ ⌊y⌋ := by
    apply Int.le_floor.mpr
    exact (Int.ceil_lt_add_one x).trans hxy |>.le
  have hcard : (((Icc (⌈x⌉ : ℤ) ⌊y⌋).ncard : ℕ) : ℤ) = ⌊y⌋ + 1 - ⌈x⌉ := by
    rw [Set.ncard_Icc]
    exact Int.card_Icc_of_le (⌈x⌉ : ℤ) ⌊y⌋
      (by omega : (⌈x⌉ : ℤ) ≤ ⌊y⌋ + 1)
  have hcardR := congrArg (fun z : ℤ => (z : ℝ)) hcard
  push_cast at hcardR
  have hfloor := Int.lt_floor_add_one y
  have hceil := Int.ceil_lt_add_one x
  linarith only [hcardR, hfloor, hceil]

/-- The exact interval of scale exponents. -/
theorem s4c_scaleWin_eq_Icc {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    scaleWin ε R = Icc (⌈Real.logb 64 (ε ^ 2 * R)⌉ : ℤ)
      ⌊Real.logb 64 (ε * R)⌋ := by
  ext j
  have hlow : 0 < ε ^ 2 * R := by positivity
  have hhigh : 0 < ε * R := mul_pos hε hR
  simp only [scaleWin, mem_ofPred_eq, mem_Icc]
  rw [Int.ceil_le, Int.le_floor,
    Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 64) hlow,
    Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 64) hhigh,
    Real.rpow_intCast]

/-- The window has at least `log₆₄(ε⁻¹) - 1` exponents. -/
theorem s4c_scaleWin_count {ε R : ℝ} (hε : 0 < ε) (hεsmall : ε < (1 / 64 : ℝ))
    (hR : 0 < R) :
    Real.logb 64 ε⁻¹ - 1 ≤ ((scaleWin ε R).ncard : ℝ) := by
  let x := Real.logb 64 (ε ^ 2 * R)
  let y := Real.logb 64 (ε * R)
  have hdiff : y - x = Real.logb 64 ε⁻¹ := by
    have hε0 : ε ≠ 0 := hε.ne'
    have hR0 : R ≠ 0 := hR.ne'
    dsimp [x, y]
    rw [Real.logb_mul hε0 hR0,
      Real.logb_mul (pow_ne_zero 2 hε0) hR0,
      Real.logb_pow, Real.logb_inv]
    ring
  have hlog : 1 < Real.logb 64 ε⁻¹ := by
    have hεi : 64 < ε⁻¹ := by
      have hi : 0 < ε⁻¹ := inv_pos.mpr hε
      have hmul : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
      nlinarith [mul_pos (sub_pos.mpr hεsmall) hi]
    simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 64)] using
      (Real.logb_lt_logb (by norm_num : (1 : ℝ) < 64)
        (by norm_num : (0 : ℝ) < 64) hεi)
  have hxy : x + 1 < y := by linarith only [hdiff, hlog]
  rw [s4c_scaleWin_eq_Icc hε hR]
  have hcount := s4c_int_interval_count hxy
  simpa only [x, y, hdiff] using hcount

/-- The scale window is finite, so it can be passed to `ShellCover`. -/
theorem s4c_scaleWin_finite {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    (scaleWin ε R).Finite := by
  rw [s4c_scaleWin_eq_Icc hε hR]
  exact Set.finite_Icc _ _

/-- Failure of the three-quarter conclusion leaves at least a quarter of
the window as candidate shells. -/
theorem s4c_bad_scale_count {S : Set ℤ} (hS : S.Finite) (p : ℤ → Prop)
    (hgood : (({j ∈ S | p j} : Set ℤ).ncard : ℝ) <
      (3 / 4 : ℝ) * (S.ncard : ℝ)) :
    (1 / 4 : ℝ) * (S.ncard : ℝ) <
      ((S \ {j ∈ S | p j}).ncard : ℝ) := by
  have hsub : {j ∈ S | p j} ⊆ S := by intro j hj; exact hj.1
  have hcard := Set.ncard_sdiff_add_ncard_of_subset hsub hS
  have hcardR := congrArg (fun n : ℕ => (n : ℝ)) hcard
  push_cast at hcardR
  linarith only [hcardR, hgood]

end HigherDimLQGMetric
