import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Summability of the Borel–Cantelli bounds (packet F2b)

* `summable_exp_mul_exp_sharp_F2b`: `∑_n e^{Dn} exp(-((√(2D) + η/2) n)² / (2 (n + C))) < ∞` for
  `η > 0`, `C > 0` — the union bound at the cube centres in (2.7) with the sharp coefficient
  `√(2d)` (planning audit MA3, Details P5);
* `summable_exp_mul_exp_sq_F2b`: `∑_n e^{Dn} exp(-(b n)² / c) < ∞` for `b, c > 0` — the cell
  suprema in (2.7).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLFPPAS.Gauss

/-- Geometric summability `∑ e^{A - δ n} < ∞`. -/
lemma summable_exp_sub_mul_F2b (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun n : ℕ => Real.exp (A - δ * n) := by
  have h := (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hδ)).mul_left (Real.exp A)
  refine h.congr fun n => ?_
  rw [← Real.exp_add]
  ring_nf

/-- The sharp union bound at the cube centres of (2.7). -/
theorem summable_exp_mul_exp_sharp_F2b {D η C : ℝ} (hD : 0 ≤ D) (hη : 0 < η) (hC : 0 < C) :
    Summable fun n : ℕ => Real.exp (D * n) *
      Real.exp (-((Real.sqrt (2 * D) + η / 2) * n) ^ 2 / (2 * (n + C))) := by
  set δ : ℝ := η ^ 2 / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  refine (summable_exp_sub_mul_F2b ((D + δ) * C) hδ0).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnC : 0 < (n : ℝ) + C := by linarith
  have hs : Real.sqrt (2 * D) ^ 2 = 2 * D := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ Real.sqrt (2 * D) := Real.sqrt_nonneg _
  have hsq : (2 * D + η ^ 2 / 4) * (n : ℝ) ^ 2 ≤ ((Real.sqrt (2 * D) + η / 2) * n) ^ 2 := by
    have : 2 * D + η ^ 2 / 4 ≤ (Real.sqrt (2 * D) + η / 2) ^ 2 := by
      nlinarith [mul_nonneg hs0 hη.le]
    calc (2 * D + η ^ 2 / 4) * (n : ℝ) ^ 2 ≤ (Real.sqrt (2 * D) + η / 2) ^ 2 * (n : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right this (sq_nonneg _)
      _ = _ := by ring
  have hquot : (D + δ) * ((n : ℝ) - C) ≤
      ((Real.sqrt (2 * D) + η / 2) * n) ^ 2 / (2 * (n + C)) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (D + δ) * ((n : ℝ) - C) * (2 * (n + C)) = (2 * D + η ^ 2 / 4) * ((n : ℝ) ^ 2 - C ^ 2) := by
      rw [hδ]
      ring
    rw [h1]
    have h2 : (2 * D + η ^ 2 / 4) * ((n : ℝ) ^ 2 - C ^ 2) ≤ (2 * D + η ^ 2 / 4) * (n : ℝ) ^ 2 := by
      have : 0 ≤ 2 * D + η ^ 2 / 4 := by positivity
      nlinarith [sq_nonneg C]
    linarith
  rw [neg_div]
  nlinarith [hquot]

/-- The cell-supremum bound of (2.7). -/
theorem summable_exp_mul_exp_sq_F2b {D b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    Summable fun n : ℕ => Real.exp (D * n) * Real.exp (-(b * n) ^ 2 / c) := by
  set a : ℝ := b ^ 2 / c with ha
  have ha0 : 0 < a := by positivity
  refine (summable_exp_sub_mul_F2b ((D + 1) ^ 2 / (4 * a)) one_pos).of_nonneg_of_le
    (fun n => by positivity) fun n => ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hsq : (b * (n : ℝ)) ^ 2 / c = a * (n : ℝ) ^ 2 := by
    rw [ha]
    field_simp
  rw [neg_div, hsq]
  have key : 0 ≤ a * ((n : ℝ) - (D + 1) / (2 * a)) ^ 2 := by positivity
  have hexp : a * ((n : ℝ) - (D + 1) / (2 * a)) ^ 2 =
      a * (n : ℝ) ^ 2 - (D + 1) * n + (D + 1) ^ 2 / (4 * a) := by
    field_simp
    ring
  nlinarith [key, hexp]

end HigherDimLFPPAS.Gauss
