import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR, part K (1): the clamped block coordinates

Task N2Z-FMVAR. Elementary facts on `fmCq`, `fmRq`, `fmSq` (`D3PlusN2FMVarDefs.lean`): on the
block they invert `fmParam`; they always satisfy the hypotheses of the energy node; and they are
Lipschitz in `q` (own elementary bookkeeping).
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace QuantumZipper
namespace D3Plus

theorem fmCl_of_mem {a b x : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : fmCl a b x = x := by
  unfold fmCl; rw [min_eq_left h2, max_eq_right h1]

theorem fmCl_ge (a b x : ℝ) : a ≤ fmCl a b x := le_max_left _ _

theorem fmCl_le {a b : ℝ} (hab : a ≤ b) (x : ℝ) : fmCl a b x ≤ b :=
  max_le hab (min_le_right _ _)

theorem abs_fmCl_sub_le (a b x y : ℝ) : |fmCl a b x - fmCl a b y| ≤ |x - y| := by
  have h1 := abs_max_sub_max_le_max a (min x b) a (min y b)
  have h2 := abs_min_sub_min_le_max x b y b
  simp only [sub_self, abs_zero] at h1 h2
  unfold fmCl
  exact h1.trans (max_le (abs_nonneg _) (h2.trans (max_le le_rfl (abs_nonneg _))))

theorem fmTq_ge (q : Fin 4 → ℝ) : 1 / 2 ≤ fmTq q := fmCl_ge _ _ _
theorem fmTq_le (q : Fin 4 → ℝ) : fmTq q ≤ 1 := fmCl_le (by norm_num) _

theorem two_pow_inv_pos (n : ℕ) : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity

theorem fmRq_pos (n : ℕ) (q : Fin 4 → ℝ) : 0 < fmRq n q :=
  mul_pos (two_pow_inv_pos n) (by linarith [fmTq_ge q])

theorem fmRq_le (n : ℕ) (q : Fin 4 → ℝ) : fmRq n q ≤ (2 : ℝ)⁻¹ ^ n := by
  unfold fmRq
  have := fmTq_le q
  have := two_pow_inv_pos n
  nlinarith

theorem fmRq_ge (n : ℕ) (q : Fin 4 → ℝ) : (2 : ℝ)⁻¹ ^ n / 2 ≤ fmRq n q := by
  unfold fmRq
  have := fmTq_ge q
  have := two_pow_inv_pos n
  nlinarith

theorem fmSq_nonneg (n : ℕ) (q : Fin 4 → ℝ) : 0 ≤ fmSq n q :=
  mul_nonneg (two_pow_inv_pos n).le (fmCl_ge _ _ _)

theorem fmSq_le (n : ℕ) (q : Fin 4 → ℝ) : fmSq n q ≤ fmRq n q := by
  unfold fmSq fmRq
  exact mul_le_mul_of_nonneg_left (fmCl_le (by linarith [fmTq_ge q]) _)
    (two_pow_inv_pos n).le

theorem two_pow_mul_inv_pow (n : ℕ) : (2 : ℝ)⁻¹ ^ n * 2 ^ n = 1 := by
  rw [← mul_pow]; norm_num

theorem fmCq_re (m n : ℕ) (q : Fin 4 → ℝ) : (fmCq m n q).re =
    (2 : ℝ)⁻¹ ^ n * fmCl (-(((m : ℝ) + 1) * 2 ^ n)) (((m : ℝ) + 1) * 2 ^ n) (q 0) := rfl

theorem fmCq_im (m n : ℕ) (q : Fin 4 → ℝ) : (fmCq m n q).im =
    (2 : ℝ)⁻¹ ^ n * fmCl (2 ^ n / ((m : ℝ) + 1)) (((m : ℝ) + 1) * 2 ^ n) (q 1) := rfl

theorem fmCq_im_ge (m n : ℕ) (q : Fin 4 → ℝ) : 1 / ((m : ℝ) + 1) ≤ (fmCq m n q).im := by
  rw [fmCq_im]
  have h := fmCl_ge (2 ^ n / ((m : ℝ) + 1)) (((m : ℝ) + 1) * 2 ^ n) (q 1)
  have h2 := two_pow_inv_pos n
  calc 1 / ((m : ℝ) + 1) = (2 : ℝ)⁻¹ ^ n * (2 ^ n / ((m : ℝ) + 1)) := by
        rw [mul_div_assoc', two_pow_mul_inv_pow]
    _ ≤ _ := mul_le_mul_of_nonneg_left h h2.le

theorem norm_fmCq_le (m n : ℕ) (q : Fin 4 → ℝ) : ‖fmCq m n q‖ ≤ 2 * ((m : ℝ) + 1) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hx : (0 : ℝ) < 2 ^ n := by positivity
  have h2 := two_pow_inv_pos n
  have hR : (2 : ℝ) ^ n / ((m : ℝ) + 1) ≤ ((m : ℝ) + 1) * 2 ^ n := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hx.le]
  have hre : |(fmCq m n q).re| ≤ (m : ℝ) + 1 := by
    rw [fmCq_re, abs_mul, abs_of_pos h2]
    have h1 := fmCl_ge (-(((m : ℝ) + 1) * 2 ^ n)) (((m : ℝ) + 1) * 2 ^ n) (q 0)
    have h3 := fmCl_le (a := -(((m : ℝ) + 1) * 2 ^ n)) (b := ((m : ℝ) + 1) * 2 ^ n)
      (by nlinarith) (q 0)
    have : |fmCl (-(((m : ℝ) + 1) * 2 ^ n)) (((m : ℝ) + 1) * 2 ^ n) (q 0)| ≤
        ((m : ℝ) + 1) * 2 ^ n := abs_le.2 ⟨h1, h3⟩
    calc (2 : ℝ)⁻¹ ^ n * |_| ≤ (2 : ℝ)⁻¹ ^ n * (((m : ℝ) + 1) * 2 ^ n) :=
          mul_le_mul_of_nonneg_left this h2.le
      _ = (m : ℝ) + 1 := by rw [mul_comm ((m : ℝ) + 1), ← mul_assoc, two_pow_mul_inv_pow, one_mul]
  have him : |(fmCq m n q).im| ≤ (m : ℝ) + 1 := by
    have h0 : 0 ≤ (fmCq m n q).im := le_trans (by positivity) (fmCq_im_ge m n q)
    rw [abs_of_nonneg h0, fmCq_im]
    have h3 := fmCl_le hR (q 1)
    calc (2 : ℝ)⁻¹ ^ n * _ ≤ (2 : ℝ)⁻¹ ^ n * (((m : ℝ) + 1) * 2 ^ n) :=
          mul_le_mul_of_nonneg_left h3 h2.le
      _ = (m : ℝ) + 1 := by rw [mul_comm ((m : ℝ) + 1), ← mul_assoc, two_pow_mul_inv_pow, one_mul]
  calc ‖fmCq m n q‖ ≤ |(fmCq m n q).re| + |(fmCq m n q).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * ((m : ℝ) + 1) := by linarith

/-! ## Inverting `fmParam` on the block -/

section Block

variable {m n : ℕ} {w : ℂ} {τ s : ℝ}

theorem fmParam_0 : fmParam n w τ s 0 = 2 ^ n * w.re := rfl
theorem fmParam_1 : fmParam n w τ s 1 = 2 ^ n * w.im := rfl
theorem fmParam_2 : fmParam n w τ s 2 = 2 ^ n * τ := rfl
theorem fmParam_3 : fmParam n w τ s 3 = 2 ^ n * s := rfl

theorem inv_pow_mul_cancel (n : ℕ) (x : ℝ) : (2 : ℝ)⁻¹ ^ n * (2 ^ n * x) = x := by
  rw [← mul_assoc, two_pow_mul_inv_pow, one_mul]

theorem fmTq_fmParam (hτ : τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n)) :
    fmTq (fmParam n w τ s) = 2 ^ n * τ := by
  have hx : (0 : ℝ) < 2 ^ n := by positivity
  unfold fmTq
  rw [fmParam_2]
  refine fmCl_of_mem ?_ ?_
  · calc (1 : ℝ) / 2 = (2 : ℝ) ^ n * (2 : ℝ)⁻¹ ^ (n + 1) := by
          rw [pow_succ, ← mul_assoc, mul_comm ((2 : ℝ) ^ n), two_pow_mul_inv_pow]; norm_num
      _ ≤ 2 ^ n * τ := mul_le_mul_of_nonneg_left hτ.1.le hx.le
  · calc (2 : ℝ) ^ n * τ ≤ 2 ^ n * (2 : ℝ)⁻¹ ^ n := mul_le_mul_of_nonneg_left hτ.2 hx.le
      _ = 1 := by rw [mul_comm, two_pow_mul_inv_pow]

theorem fmRq_fmParam (hτ : τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n)) :
    fmRq n (fmParam n w τ s) = τ := by
  unfold fmRq; rw [fmTq_fmParam hτ, inv_pow_mul_cancel]

theorem fmSq_fmParam (hτ : τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n)) (hs : s ∈ Ioo 0 τ) :
    fmSq n (fmParam n w τ s) = s := by
  have hx : (0 : ℝ) < 2 ^ n := by positivity
  unfold fmSq
  rw [fmTq_fmParam hτ, fmParam_3, fmCl_of_mem (mul_pos hx hs.1).le
    (mul_le_mul_of_nonneg_left hs.2.le hx.le), inv_pow_mul_cancel]

theorem fmCq_fmParam (hw : w ∈ fmBox m) : fmCq m n (fmParam n w τ s) = w := by
  have hx : (0 : ℝ) < 2 ^ n := by positivity
  have hm : ‖w‖ ≤ m := hw.1
  have hre : |w.re| ≤ m := (Complex.abs_re_le_norm w).trans hm
  have him : w.im ≤ m := (Complex.im_le_norm w).trans hm
  apply Complex.ext
  · rw [fmCq_re, fmParam_0, fmCl_of_mem, inv_pow_mul_cancel]
    · have := (abs_le.1 hre).1
      nlinarith
    · have := (abs_le.1 hre).2
      nlinarith
  · rw [fmCq_im, fmParam_1, fmCl_of_mem, inv_pow_mul_cancel]
    · rw [div_le_iff₀ (by positivity)]
      have h := hw.2
      rw [div_le_iff₀ (by positivity)] at h
      nlinarith
    · nlinarith

end Block

/-! ## Lipschitz bounds -/

theorem abs_coord_sub_le (q q' : Fin 4 → ℝ) (i : Fin 4) : |q i - q' i| ≤ ‖q - q'‖ := by
  have := norm_le_pi_norm (q - q') i
  simpa [Real.norm_eq_abs] using this

/-- The clamped parameters move by at most `4 · 2^{-n} ‖q − q'‖` (sum of the three). -/
theorem fmParams_lip (m n : ℕ) (q q' : Fin 4 → ℝ) :
    ‖fmCq m n q - fmCq m n q'‖ + |fmRq n q - fmRq n q'| + |fmSq n q - fmSq n q'| ≤
      4 * (2 : ℝ)⁻¹ ^ n * ‖q - q'‖ := by
  set D : ℝ := ‖q - q'‖ with hD
  have h2 := two_pow_inv_pos n
  have hre : |(fmCq m n q - fmCq m n q').re| ≤ (2 : ℝ)⁻¹ ^ n * D := by
    rw [Complex.sub_re, fmCq_re, fmCq_re, ← mul_sub, abs_mul, abs_of_pos h2]
    exact mul_le_mul_of_nonneg_left ((abs_fmCl_sub_le _ _ _ _).trans (abs_coord_sub_le q q' 0))
      h2.le
  have him : |(fmCq m n q - fmCq m n q').im| ≤ (2 : ℝ)⁻¹ ^ n * D := by
    rw [Complex.sub_im, fmCq_im, fmCq_im, ← mul_sub, abs_mul, abs_of_pos h2]
    exact mul_le_mul_of_nonneg_left ((abs_fmCl_sub_le _ _ _ _).trans (abs_coord_sub_le q q' 1))
      h2.le
  have ht : |fmTq q - fmTq q'| ≤ D := (abs_fmCl_sub_le _ _ _ _).trans (abs_coord_sub_le q q' 2)
  have hr : |fmRq n q - fmRq n q'| ≤ (2 : ℝ)⁻¹ ^ n * D := by
    unfold fmRq; rw [← mul_sub, abs_mul, abs_of_pos h2]
    exact mul_le_mul_of_nonneg_left ht h2.le
  have hs : |fmSq n q - fmSq n q'| ≤ (2 : ℝ)⁻¹ ^ n * D := by
    unfold fmSq; rw [← mul_sub, abs_mul, abs_of_pos h2]
    refine mul_le_mul_of_nonneg_left ?_ h2.le
    unfold fmCl
    refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
    rw [sub_self, abs_zero]
    exact max_le (norm_nonneg _)
      ((abs_min_sub_min_le_max _ _ _ _).trans (max_le (abs_coord_sub_le q q' 3) ht))
  have hn := Complex.norm_le_abs_re_add_abs_im (fmCq m n q - fmCq m n q')
  nlinarith

end D3Plus
end QuantumZipper
