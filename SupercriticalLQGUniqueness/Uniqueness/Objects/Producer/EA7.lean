import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA6
import SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachmentCore.FinalCore




 
















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Complex
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Producer

 
theorem coeff_le_K {H r : ℝ} {k : ℕ} (hr : 0 < r) (hH : (1 / 2 : ℝ) ^ (k + 1) * r ≤ H) :
    (H / r) ^ (-(1 : ℝ) / 4) ≤ (2 : ℝ) ^ (((k : ℝ) + 1) / 4) := by
  have hpos : 0 < (1 / 2 : ℝ) ^ (k + 1) := by positivity
  have hx : (1 / 2 : ℝ) ^ (k + 1) ≤ H / r := by rw [le_div_iff₀ hr]; exact hH
  have h1 : (H / r) ^ (-(1 : ℝ) / 4) ≤ ((1 / 2 : ℝ) ^ (k + 1)) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos hpos hx (by norm_num)
  refine h1.trans (le_of_eq ?_)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  congr 1
  push_cast
  ring

 
theorem time_low_k {H r a : ℝ} {k : ℕ} (hr : 0 < r) (ha : 0 ≤ a)
    (hH : (1 / 2 : ℝ) ^ (k + 1) * r ≤ H) :
    (2 : ℝ) ^ (-((k : ℝ) + 3) * a) ≤ (H / (4 * r)) ^ a := by
  have hpos : 0 < (1 / 2 : ℝ) ^ (k + 3) := by positivity
  have hx : (1 / 2 : ℝ) ^ (k + 3) ≤ H / (4 * r) := by
    rw [le_div_iff₀ (by positivity)]
    have : (1 / 2 : ℝ) ^ (k + 3) * (4 * r) = (1 / 2 : ℝ) ^ (k + 1) * r := by
      rw [pow_add, pow_add]; ring
    linarith
  refine le_trans (le_of_eq ?_) (Real.rpow_le_rpow hpos.le hx ha)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
  congr 1
  push_cast
  ring

 
theorem order_of_disjoint_images {P : ℝ → ℂ} {s t s' t' : ℝ} {A B : Set ℂ} (hAB : Disjoint A B)
    (hst : s ≤ t) (hst' : s' ≤ t') (hA : MapsTo P (Icc s t) A) (hB : MapsTo P (Icc s' t') B) :
    t < s' ∨ t' < s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  set τ := max s s' with hτ
  have hτ1 : τ ∈ Icc s t := ⟨le_max_left _ _, max_le hst h1⟩
  have hτ2 : τ ∈ Icc s' t' := ⟨le_max_right _ _, max_le h2 hst'⟩
  exact Set.disjoint_left.1 hAB (hA hτ1) (hB hτ2)

end SupercriticalLQGUniqueness.Uniqueness.Objects.Producer
