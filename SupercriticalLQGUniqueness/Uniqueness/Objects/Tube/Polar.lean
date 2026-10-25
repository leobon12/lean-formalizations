import Mathlib




 










set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

 
def ex (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

 
def pol (R θ : ℝ) : ℂ := (R : ℂ) * ex θ

theorem ex_re (θ : ℝ) : (ex θ).re = Real.cos θ := by
  unfold ex; exact Complex.exp_ofReal_mul_I_re θ

theorem ex_im (θ : ℝ) : (ex θ).im = Real.sin θ := by
  unfold ex; exact Complex.exp_ofReal_mul_I_im θ

theorem norm_ex (θ : ℝ) : ‖ex θ‖ = 1 := by
  unfold ex; exact Complex.norm_exp_ofReal_mul_I θ

theorem ex_ne_zero (θ : ℝ) : ex θ ≠ 0 := by
  unfold ex; exact Complex.exp_ne_zero _

theorem ex_add (a b : ℝ) : ex (a + b) = ex a * ex b := by
  unfold ex; push_cast; rw [← Complex.exp_add]; ring_nf

theorem ex_zero : ex 0 = 1 := by simp [ex]

theorem ex_neg (a : ℝ) : ex (-a) = (ex a)⁻¹ := by
  unfold ex; push_cast; rw [← Complex.exp_neg]; ring_nf

theorem ex_pi : ex π = -1 := by
  unfold ex; exact Complex.exp_pi_mul_I

theorem ex_add_pi (a : ℝ) : ex (a + π) = -ex a := by
  rw [ex_add, ex_pi]; ring

theorem ex_mul_ex_neg (a : ℝ) : ex a * ex (-a) = 1 := by
  rw [← ex_add, add_neg_cancel, ex_zero]

theorem ex_eq_cos_add_sin (θ : ℝ) : ex θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
  apply Complex.ext
  · simp only [ex_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im]; ring
  · simp only [ex_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_re, Complex.I_im]; ring

theorem ex_two_pi : ex (2 * π) = 1 := by
  unfold ex; push_cast; exact Complex.exp_two_pi_mul_I

theorem ex_add_two_pi (a : ℝ) : ex (a + 2 * π) = ex a := by
  rw [ex_add, ex_two_pi, mul_one]

theorem ex_add_int_mul_two_pi (a : ℝ) (m : ℤ) : ex (a + m * (2 * π)) = ex a := by
  rw [ex_add]
  have : ex (m * (2 * π)) = 1 := by
    unfold ex; push_cast
    rw [show (m : ℂ) * (2 * π) * I = m * (2 * π * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I m
  rw [this, mul_one]

theorem pol_re (R θ : ℝ) : (pol R θ).re = R * Real.cos θ := by
  unfold pol; rw [Complex.re_ofReal_mul, ex_re]

theorem pol_im (R θ : ℝ) : (pol R θ).im = R * Real.sin θ := by
  unfold pol; rw [Complex.im_ofReal_mul, ex_im]

theorem norm_pol {R : ℝ} (hR : 0 ≤ R) (θ : ℝ) : ‖pol R θ‖ = R := by
  unfold pol; rw [norm_mul, norm_ex, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR, mul_one]

theorem pol_zero_left (θ : ℝ) : pol 0 θ = 0 := by simp [pol]

theorem pol_add_pi (R θ : ℝ) : pol R (θ + π) = -pol R θ := by
  unfold pol; rw [ex_add_pi]; ring

theorem pol_pi (R : ℝ) : pol R π = -(R : ℂ) := by
  unfold pol; rw [ex_pi]; ring

theorem pol_zero_right (R : ℝ) : pol R 0 = (R : ℂ) := by
  unfold pol; rw [ex_zero, mul_one]

theorem ex_mul_pol (a R θ : ℝ) : ex a * pol R θ = pol R (θ + a) := by
  unfold pol; rw [ex_add]; ring

 
theorem re_ex_mul_pol (a R θ : ℝ) : (ex a * pol R θ).re = R * Real.cos (θ + a) := by
  rw [ex_mul_pol, pol_re]

theorem dist_eq_norm_sub' (x y : ℂ) : dist x y = ‖x - y‖ := Complex.dist_eq x y

 
theorem norm_gap_le_dist (x y : ℂ) : |‖x‖ - ‖y‖| ≤ dist x y := by
  rw [Complex.dist_eq]; exact abs_norm_sub_norm_le x y

 
theorem re_gap_le_dist (c x y : ℂ) (hc : ‖c‖ = 1) : |(c * x).re - (c * y).re| ≤ dist x y := by
  rw [Complex.dist_eq, ← Complex.sub_re, ← mul_sub]
  calc |(c * (x - y)).re| ≤ ‖c * (x - y)‖ := Complex.abs_re_le_norm _
    _ = ‖x - y‖ := by rw [norm_mul, hc, one_mul]

 
theorem normSq_ex_sub (a b : ℝ) : ‖ex a - ex b‖ ^ 2 = 2 - 2 * Real.cos (a - b) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, ex_re, ex_im]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

 
theorem normSq_pol_sub (R S a b : ℝ) :
    ‖pol R a - pol S b‖ ^ 2 = R ^ 2 + S ^ 2 - 2 * R * S * Real.cos (a - b) := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, pol_re, pol_im]
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b]

 
theorem norm_ex_sub_le (a b : ℝ) : ‖ex a - ex b‖ ≤ |a - b| := by
  have h1 : ‖ex a - ex b‖ ^ 2 ≤ (a - b) ^ 2 := by
    rw [normSq_ex_sub]
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := a - b)]
  have h2 : 0 ≤ ‖ex a - ex b‖ := norm_nonneg _
  nlinarith [abs_nonneg (a - b), sq_abs (a - b)]

 
theorem norm_pol_sub_pol_le (R a b : ℝ) : ‖pol R a - pol R b‖ ≤ |R| * |a - b| := by
  unfold pol
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_ex_sub_le a b) (abs_nonneg R)

 
theorem norm_pol_sub_pol_same_angle (R S a : ℝ) : ‖pol R a - pol S a‖ = |R - S| := by
  unfold pol
  rw [← sub_mul, norm_mul, norm_ex, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]

 

 

def polarPath (R₁ R₂ φ₁ φ₂ : ℝ) : Path (pol R₁ φ₁) (pol R₂ φ₂) where
  toFun t := pol (R₁ + (t : ℝ) * (R₂ - R₁)) (φ₁ + (t : ℝ) * (φ₂ - φ₁))
  continuous_toFun := by unfold pol ex; fun_prop
  source' := by simp
  target' := by simp

theorem polarPath_apply (R₁ R₂ φ₁ φ₂ : ℝ) (t : unitInterval) :
    polarPath R₁ R₂ φ₁ φ₂ t = pol (R₁ + (t : ℝ) * (R₂ - R₁)) (φ₁ + (t : ℝ) * (φ₂ - φ₁)) := rfl

 
theorem lerp_mem_uIcc (a b : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    a + t * (b - a) ∈ uIcc a b := by
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    exact ⟨by nlinarith, by nlinarith⟩
  · rw [uIcc_of_ge h]
    exact ⟨by nlinarith, by nlinarith⟩

 

theorem mem_range_polarPath {R₁ R₂ φ₁ φ₂ : ℝ} {x : ℂ} (hx : x ∈ range (polarPath R₁ R₂ φ₁ φ₂)) :
    ∃ R ∈ uIcc R₁ R₂, ∃ φ ∈ uIcc φ₁ φ₂, x = pol R φ := by
  obtain ⟨t, rfl⟩ := hx
  exact ⟨_, lerp_mem_uIcc R₁ R₂ t.2.1 t.2.2, _, lerp_mem_uIcc φ₁ φ₂ t.2.1 t.2.2, rfl⟩

 
theorem mem_range_polarPath_spoke {R₁ R₂ φ : ℝ} {x : ℂ} (hx : x ∈ range (polarPath R₁ R₂ φ φ)) :
    ∃ R ∈ uIcc R₁ R₂, x = pol R φ := by
  obtain ⟨R, hR, φ', hφ', rfl⟩ := mem_range_polarPath hx
  rw [uIcc_self, mem_singleton_iff] at hφ'
  exact ⟨R, hR, by rw [hφ']⟩

 
theorem mem_range_polarPath_arc {R φ₁ φ₂ : ℝ} {x : ℂ} (hx : x ∈ range (polarPath R R φ₁ φ₂)) :
    ∃ φ ∈ uIcc φ₁ φ₂, x = pol R φ := by
  obtain ⟨R', hR', φ, hφ, rfl⟩ := mem_range_polarPath hx
  rw [uIcc_self, mem_singleton_iff] at hR'
  exact ⟨φ, hφ, by rw [hR']⟩

 
def segPath (a b : ℂ) : Path a b where
  toFun t := a + ((t : ℝ) : ℂ) * (b - a)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem segPath_apply (a b : ℂ) (t : unitInterval) : segPath a b t = a + ((t : ℝ) : ℂ) * (b - a) :=
  rfl

theorem range_segPath_subset (a b : ℂ) : range (segPath a b) ⊆ segment ℝ a b := by
  rintro _ ⟨t, rfl⟩
  rw [segPath_apply, segment_eq_image_lineMap]
  refine ⟨t, ⟨t.2.1, t.2.2⟩, ?_⟩
  rw [AffineMap.lineMap_apply_module']
  simp only [Complex.real_smul]
  ring

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
