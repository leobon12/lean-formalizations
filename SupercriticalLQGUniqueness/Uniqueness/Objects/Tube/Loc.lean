import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Geom




 









set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

theorem InSector.rotate {w : ℂ} {m a b : ℝ} (h : InSector w m a b) (c : ℝ) :
    InSector (ex c * w) m (a + c) (b + c) := by
  obtain ⟨R, hR, φ, hφ, rfl⟩ := h
  exact ⟨R, hR, φ + c, ⟨by linarith [hφ.1], by linarith [hφ.2]⟩, ex_mul_pol c R φ⟩

namespace TubeParams

variable {P : TubeParams} {r : ℝ}

 

theorem dist_modMap_site_le (hP : P.Good) (hr : 0 < r) (k : ℤ) {ζ : ℂ} {A : ℝ} (hζ : ‖ζ‖ ≤ A) :
    dist (P.modMap r k ζ) (P.site r k) ≤ A * (P.ρ * r) := by
  rw [dist_modMap_site hP.n_norm (mul_pos hP.ρ_pos hr).le]
  nlinarith [mul_pos hP.ρ_pos hr]

theorem norm_site (hr : 0 < r) (k : ℤ) : ‖P.site r k‖ = 2 * r := norm_pol (by linarith) _

 
theorem inSector_of_near_site (hP : P.Good) (hr : 0 < r) (k : ℤ) {x : ℂ}
    (hx : dist x (P.site r k) ≤ 5 * (P.ρ * r)) :
    InSector x (2 * r - 5 * (P.ρ * r)) (P.ω k - 5 * P.ρ) (P.ω k + 5 * P.ρ) := by
  have hρ := hP.ρ_le
  have h := inSector_of_near (R := 2 * r) (θ := P.ω k) (ε := 5 * (P.ρ * r)) (by linarith)
    (by nlinarith [hP.ρ_pos]) (by nlinarith [hP.ρ_pos]) hx
  have e : 2 * (5 * (P.ρ * r)) / (2 * r) = 5 * P.ρ := by field_simp
  rw [e] at h
  exact h

theorem norm_bounds_of_near_site (hr : 0 < r) (k : ℤ) {x : ℂ} {e : ℝ}
    (hx : dist x (P.site r k) ≤ e) : 2 * r - e ≤ ‖x‖ ∧ ‖x‖ ≤ 2 * r + e := by
  have h1 := norm_le_norm_add_norm_sub' x (P.site r k)
  have h2 := norm_le_norm_add_norm_sub' (P.site r k) x
  rw [Complex.dist_eq] at hx
  rw [norm_site hr] at h1 h2
  rw [norm_sub_rev] at h2
  constructor <;> linarith

 

 
theorem corridor_rot_mid (hn : ‖P.n‖ = 1) (hK : (P.K : ℝ) ≠ 0) (k : ℤ) (τ : ℝ) :
    ex (-(P.ω k + π / P.K)) * (P.gatePlus r k + (τ : ℂ) * (P.gateMinus r (k + 1) - P.gatePlus r k)) =
      ex (-(π / P.K)) * ((2 * r : ℝ) + ((4 * P.ρ * r : ℝ) : ℂ) * Complex.I) + (τ : ℂ) *
        (ex (π / P.K) * ((2 * r : ℝ) - ((4 * P.ρ * r : ℝ) : ℂ) * Complex.I) -
          ex (-(π / P.K)) * ((2 * r : ℝ) + ((4 * P.ρ * r : ℝ) : ℂ) * Complex.I)) := by
  rw [gatePlus_eq hn, gateMinus_eq hn]
  unfold site tangent pol
  rw [ω_add_one hK]
  have e1 : ex (-(P.ω k + π / P.K)) = ex (-P.ω k) * ex (-(π / P.K)) := by rw [← ex_add]; ring_nf
  have e2 : ex (P.ω k + 2 * π / P.K) = ex (P.ω k) * ex (π / P.K) * ex (π / P.K) := by
    rw [← ex_add, ← ex_add]; ring_nf
  have e3 : ex (-(π / P.K)) * ex (π / P.K) = 1 := by rw [mul_comm, ex_mul_ex_neg]
  have hF : ex (-P.ω k) * ex (P.ω k) = 1 := by rw [mul_comm, ex_mul_ex_neg]
  rw [e1, e2]
  set E := ex (P.ω k)
  set F := ex (-P.ω k)
  set H := ex (π / P.K)
  set G := ex (-(π / P.K))
  push_cast
  linear_combination (G * (2 * (r : ℂ) + 4 * (P.ρ : ℂ) * r * Complex.I) + (τ : ℂ) *
      (G * H * H * (2 * (r : ℂ) - 4 * (P.ρ : ℂ) * r * Complex.I) - G * (2 * (r : ℂ) +
        4 * (P.ρ : ℂ) * r * Complex.I))) * hF
    + ((τ : ℂ) * H * (2 * (r : ℂ) - 4 * (P.ρ : ℂ) * r * Complex.I)) * e3

 
theorem corridor_inSector (hP : P.Good) (hr : 0 < r) (k : ℤ) {y : ℂ}
    (hy : y ∈ segment ℝ (P.gatePlus r k) (P.gateMinus r (k + 1))) :
    InSector y (2 * r * Real.cos (π / P.K)) (P.ω k) (P.ω (k + 1)) := by
  have hK := hP.K_pos
  set h := π / (P.K : ℝ) with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h < π / 2 := by
    rw [hh, div_lt_div_iff₀ hK (by norm_num : (0 : ℝ) < 2)]
    nlinarith [Real.pi_pos, hP.K_ge]
  have hcos : 0 < Real.cos h := Real.cos_pos_of_mem_Ioo ⟨by linarith, hh1⟩
  have hsin : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi hh0 (by linarith)
  have hρ := hP.ρ_pos
  
  have hsin2 : 2 * P.ρ ≤ Real.sin h := by
    have := Real.mul_le_sin hh0.le hh1.le
    have e : 2 / π * h = 2 / P.K := by rw [hh]; field_simp
    rw [e] at this
    have : 2 * P.ρ ≤ 2 / P.K := by rw [le_div_iff₀ hK]; nlinarith [hP.ρK_le]
    linarith
  rw [segment_eq_image'] at hy
  obtain ⟨τ, hτ, rfl⟩ := hy
  dsimp only
  rw [Complex.real_smul]
  set w := ex (-(P.ω k + h)) * (P.gatePlus r k + (τ : ℂ) * (P.gateMinus r (k + 1) - P.gatePlus r k))
    with hw
  have hw' := corridor_rot_mid (r := r) hP.n_norm hP.K_ne k τ
  rw [← hh, ← hw] at hw'
  set X₀ := 2 * r * Real.cos h + 4 * P.ρ * r * Real.sin h with hX₀def
  set Y₀ := 2 * r * Real.sin h - 4 * P.ρ * r * Real.cos h with hY₀def
  have hre : w.re = X₀ := by
    rw [hw']
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im, ex_re, ex_im,
      Real.cos_neg, Real.sin_neg]
    ring
  have him : w.im = (2 * τ - 1) * Y₀ := by
    rw [hw']
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.sub_im, ex_re, ex_im,
      Real.cos_neg, Real.sin_neg]
    ring
  have hY₀ : 0 ≤ Y₀ := by
    rw [hY₀def]; nlinarith [Real.cos_le_one h, mul_pos hρ hr]
  have hX₀ : 2 * r * Real.cos h ≤ X₀ := by
    rw [hX₀def]; nlinarith [mul_pos hρ hr]
  have hX₀pos : 0 < X₀ := lt_of_lt_of_le (by positivity) hX₀
  have hsec : InSector w X₀ (-h) h := by
    rw [← hre]
    apply inSector_of_re_im hh0.le hh1 (by rw [hre]; exact hX₀pos)
    rw [him, hre, Real.tan_eq_sin_div_cos, abs_mul]
    have h1 : |2 * τ - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
    have h2 : Y₀ * Real.cos h ≤ Real.sin h * X₀ := by
      rw [hY₀def, hX₀def]; nlinarith [Real.sin_sq_add_cos_sq h, mul_pos hρ hr]
    rw [abs_of_nonneg hY₀, div_mul_eq_mul_div, le_div_iff₀ hcos]
    calc |2 * τ - 1| * Y₀ * Real.cos h ≤ 1 * Y₀ * Real.cos h := by
          apply mul_le_mul_of_nonneg_right _ hcos.le
          exact mul_le_mul_of_nonneg_right h1 hY₀
      _ ≤ Real.sin h * X₀ := by linarith
  have hrot := hsec.rotate (P.ω k + h)
  have hyw : ex (P.ω k + h) * w = P.gatePlus r k + (τ : ℂ) * (P.gateMinus r (k + 1) - P.gatePlus r k) := by
    rw [hw, ← mul_assoc, ← ex_add, add_neg_cancel, ex_zero, one_mul]
  rw [hyw] at hrot
  refine hrot.mono hX₀ (by linarith) ?_
  rw [ω_add_one hP.K_ne, hh]; ring_nf; linarith

theorem corridor_norm_le (hP : P.Good) (hr : 0 < r) (k : ℤ) {y : ℂ}
    (hy : y ∈ segment ℝ (P.gatePlus r k) (P.gateMinus r (k + 1))) : ‖y‖ ≤ 2 * r + 4 * (P.ρ * r) := by
  have h1 : ‖P.gatePlus r k‖ ≤ 2 * r + 4 * (P.ρ * r) := by
    rw [gatePlus_eq hP.n_norm]
    calc ‖P.site r k + ((4 * P.ρ * r : ℝ) : ℂ) * P.tangent k‖
        ≤ ‖P.site r k‖ + ‖((4 * P.ρ * r : ℝ) : ℂ) * P.tangent k‖ := norm_add_le _ _
      _ = 2 * r + 4 * (P.ρ * r) := by
          rw [norm_site hr, norm_mul, norm_tangent, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by nlinarith [hP.ρ_pos])]; ring
  have h2 : ‖P.gateMinus r (k + 1)‖ ≤ 2 * r + 4 * (P.ρ * r) := by
    rw [gateMinus_eq hP.n_norm]
    calc ‖P.site r (k + 1) - ((4 * P.ρ * r : ℝ) : ℂ) * P.tangent (k + 1)‖
        ≤ ‖P.site r (k + 1)‖ + ‖((4 * P.ρ * r : ℝ) : ℂ) * P.tangent (k + 1)‖ := norm_sub_le _ _
      _ = 2 * r + 4 * (P.ρ * r) := by
          rw [norm_site hr, norm_mul, norm_tangent, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by nlinarith [hP.ρ_pos])]; ring
  have hconv : Convex ℝ (closedBall (0 : ℂ) (2 * r + 4 * (P.ρ * r))) := convex_closedBall _ _
  have := hconv.segment_subset (mem_closedBall_zero_iff.mpr h1) (mem_closedBall_zero_iff.mpr h2) hy
  exact mem_closedBall_zero_iff.mp this

 
theorem two_r_cos_ge (hP : P.Good) (hr : 0 < r) :
    2 * r - 10 * (P.ρ * r) ≤ 2 * r * Real.cos (π / P.K) := by
  have h1 := Real.one_sub_sq_div_two_le_cos (x := π / P.K)
  have h2 : (π / P.K) ^ 2 = π ^ 2 / (P.K : ℝ) ^ 2 := by rw [div_pow]
  have h3 := hP.loc
  nlinarith

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
