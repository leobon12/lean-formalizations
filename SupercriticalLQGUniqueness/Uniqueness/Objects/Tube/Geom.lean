import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Tube
import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Sector




 











set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

 

structure Good (P : TubeParams) : Prop where
  ρ_pos : 0 < P.ρ
  α_gt : 3 / 4 < P.α
  α_lt : P.α < 1
  sp_pos : 0 < P.sp
  sp_le : 100 * P.sp ≤ 1 - P.α
  wp_pos : 0 < P.wp
  wp_le : 100 * P.wp ≤ P.sp
  ψu_mem : P.ψu ∈ Icc (-(π / 2)) (π / 2)
  ψv_mem : P.ψv ∈ Icc (-(π / 2)) (π / 2)
  n_norm : ‖P.n‖ = 1
  K_ge : (100 : ℝ) ≤ P.K
  ρK_le : P.ρ * P.K ≤ 1 / 10 ^ 6
  loc : π ^ 2 / (P.K : ℝ) ^ 2 ≤ 10 * P.ρ

variable {P : TubeParams} {r : ℝ}

section Basic

variable (hP : P.Good)
include hP

theorem Good.K_pos : (0 : ℝ) < P.K := by linarith [hP.K_ge]

theorem Good.K_ne : (P.K : ℝ) ≠ 0 := hP.K_pos.ne'

theorem Good.n_ne : P.n ≠ 0 := by
  intro h; have := hP.n_norm; rw [h, norm_zero] at this; norm_num at this

theorem Good.ρ_le : P.ρ ≤ 1 / 10 ^ 8 := by
  have h1 := hP.ρK_le
  have h2 := hP.K_ge
  have hρ := hP.ρ_pos
  nlinarith

theorem Good.sp_le' : P.sp ≤ 1 / 400 := by
  have := hP.sp_le; have := hP.α_gt; linarith

theorem Good.sp_le_two_thirds : P.sp ≤ 2 / 3 := by linarith [hP.sp_le']

theorem Good.u_minus_pos : 0 ≤ P.α - 3 * P.sp / 4 := by
  have := hP.sp_le'; have := hP.α_gt; linarith

 
theorem Good.pi_div_K_ge : 10 ^ 6 * P.ρ ≤ π / P.K := by
  have hK := hP.K_pos
  rw [le_div_iff₀ hK]
  have := hP.ρK_le
  nlinarith [Real.pi_gt_three]

end Basic

theorem ω_add_one (hK : (P.K : ℝ) ≠ 0) (k : ℤ) : P.ω (k + 1) = P.ω k + 2 * π / P.K := by
  unfold ω; push_cast; field_simp

theorem ω_add_K (hK : (P.K : ℝ) ≠ 0) (k : ℤ) : P.ω (k + P.K) = P.ω k + 2 * π := by
  unfold ω; push_cast; field_simp

theorem ω_sub (hK : (P.K : ℝ) ≠ 0) (j k : ℤ) : P.ω j - P.ω k = 2 * π * (j - k) / P.K := by
  unfold ω; field_simp

theorem site_add_K (hK : (P.K : ℝ) ≠ 0) (k : ℤ) : P.site r (k + P.K) = P.site r k := by
  unfold site pol; rw [ω_add_K hK, ex_add_two_pi]

theorem tangent_add_K (hK : (P.K : ℝ) ≠ 0) (k : ℤ) : P.tangent (k + P.K) = P.tangent k := by
  unfold tangent; rw [ω_add_K hK, ex_add_two_pi]

theorem twist_add_K (hK : (P.K : ℝ) ≠ 0) (k : ℤ) : P.twist (k + P.K) = P.twist k := by
  unfold twist; rw [tangent_add_K hK]

theorem modMap_add_K (hK : (P.K : ℝ) ≠ 0) (k : ℤ) (ζ : ℂ) :
    P.modMap r (k + P.K) ζ = P.modMap r k ζ := by
  unfold modMap; rw [site_add_K hK]

theorem norm_tangent (k : ℤ) : ‖P.tangent k‖ = 1 := by
  unfold tangent; rw [norm_mul, Complex.norm_I, norm_ex, one_mul]

theorem tangent_ne (k : ℤ) : P.tangent k ≠ 0 := by
  intro h; have := norm_tangent (P := P) k; rw [h, norm_zero] at this; norm_num at this

 
theorem ex_twist (hn : ‖P.n‖ = 1) (k : ℤ) : ex (P.twist k) = P.tangent k / P.n := by
  have h1 : ‖P.tangent k / P.n‖ = 1 := by rw [norm_div, norm_tangent, hn, div_one]
  have := pol_norm_arg (P.tangent k / P.n)
  rw [h1] at this
  unfold pol at this
  rw [Complex.ofReal_one, one_mul] at this
  exact this

theorem n_mul_ex_twist (hn : ‖P.n‖ = 1) (k : ℤ) : P.n * ex (P.twist k) = P.tangent k := by
  have hn0 : P.n ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  rw [ex_twist hn, mul_div_cancel₀ _ hn0]

 

theorem modMap_sub (k : ℤ) (ζ ζ' : ℂ) :
    P.modMap r k ζ - P.modMap r k ζ' = ((P.ρ * r : ℝ) : ℂ) * P.n * (ζ - ζ') := by
  unfold modMap; ring

theorem dist_modMap (hn : ‖P.n‖ = 1) (hρr : 0 ≤ P.ρ * r) (k : ℤ) (ζ ζ' : ℂ) :
    dist (P.modMap r k ζ) (P.modMap r k ζ') = P.ρ * r * dist ζ ζ' := by
  rw [Complex.dist_eq, modMap_sub, norm_mul, norm_mul, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hρr, mul_one, Complex.dist_eq]

theorem dist_modMap_site (hn : ‖P.n‖ = 1) (hρr : 0 ≤ P.ρ * r) (k : ℤ) (ζ : ℂ) :
    dist (P.modMap r k ζ) (P.site r k) = P.ρ * r * ‖ζ‖ := by
  rw [Complex.dist_eq]
  unfold modMap
  rw [add_sub_cancel_left, norm_mul, norm_mul, hn, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hρr, mul_one]

 
def frameInv (P : TubeParams) (r : ℝ) (k : ℤ) (y : ℂ) : ℂ := ((P.ρ * r : ℝ) : ℂ)⁻¹ * P.n⁻¹ * (y - P.site r k)

theorem modMap_frameInv (hn : P.n ≠ 0) (hρr : P.ρ * r ≠ 0) (k : ℤ) (y : ℂ) :
    P.modMap r k (P.frameInv r k y) = y := by
  unfold modMap frameInv
  have : ((P.ρ * r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hρr
  field_simp
  ring

 

theorem gatePlus_eq (hn : ‖P.n‖ = 1) (k : ℤ) :
    P.gatePlus r k = P.site r k + ((4 * P.ρ * r : ℝ) : ℂ) * P.tangent k := by
  unfold gatePlus modMap pol
  rw [← n_mul_ex_twist hn]; push_cast; ring

theorem gateMinus_eq (hn : ‖P.n‖ = 1) (k : ℤ) :
    P.gateMinus r k = P.site r k - ((4 * P.ρ * r : ℝ) : ℂ) * P.tangent k := by
  unfold gateMinus modMap pol
  rw [ex_add_pi, ← n_mul_ex_twist hn]; push_cast; ring

 

 
theorem corridor_rot_out (hn : ‖P.n‖ = 1) (hK : (P.K : ℝ) ≠ 0) (k : ℤ) (τ : ℝ) :
    -Complex.I * ex (-P.ω k) *
        (P.gatePlus r k + (τ : ℂ) * (P.gateMinus r (k + 1) - P.gatePlus r k) - P.site r k) =
      ((4 * P.ρ * r : ℝ) : ℂ) + (τ : ℂ) * (-(2 * r : ℝ) * Complex.I * ex (2 * π / P.K)
        - ((4 * P.ρ * r : ℝ) : ℂ) * ex (2 * π / P.K) + (2 * r : ℝ) * Complex.I
        - ((4 * P.ρ * r : ℝ) : ℂ)) := by
  rw [gatePlus_eq hn, gateMinus_eq hn]
  unfold site tangent pol
  rw [ω_add_one hK, ex_add]
  have hF : ex (-P.ω k) * ex (P.ω k) = 1 := by rw [mul_comm, ex_mul_ex_neg]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  set E := ex (P.ω k)
  set F := ex (-P.ω k)
  set T := ex (2 * π / P.K)
  linear_combination (-4 * (P.ρ : ℂ) * r * (Complex.I * Complex.I) + (τ : ℂ) * (-2 * (r : ℂ) *
      Complex.I * T + 4 * (P.ρ : ℂ) * r * (Complex.I * Complex.I) * T + 2 * (r : ℂ) * Complex.I +
      4 * (P.ρ : ℂ) * r * (Complex.I * Complex.I))) * hF
    + (-4 * (P.ρ : ℂ) * r + 4 * (P.ρ : ℂ) * r * τ * (T + 1)) * hI

 
theorem corridor_rot_in (hn : ‖P.n‖ = 1) (hK : (P.K : ℝ) ≠ 0) (k : ℤ) (τ : ℝ) :
    Complex.I * ex (-P.ω (k + 1)) *
        (P.gatePlus r k + (τ : ℂ) * (P.gateMinus r (k + 1) - P.gatePlus r k) - P.site r (k + 1)) =
      ((4 * P.ρ * r : ℝ) : ℂ) + ((1 - τ : ℝ) : ℂ) * ((2 * r : ℝ) * Complex.I * ex (-(2 * π / P.K))
        - ((4 * P.ρ * r : ℝ) : ℂ) * ex (-(2 * π / P.K)) - (2 * r : ℝ) * Complex.I
        - ((4 * P.ρ * r : ℝ) : ℂ)) := by
  rw [gatePlus_eq hn, gateMinus_eq hn]
  have hω : P.ω k = P.ω (k + 1) + -(2 * π / P.K) := by rw [ω_add_one hK]; ring
  unfold site tangent pol
  rw [hω, ex_add]
  have hF : ex (-P.ω (k + 1)) * ex (P.ω (k + 1)) = 1 := by rw [mul_comm, ex_mul_ex_neg]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  set E := ex (P.ω (k + 1))
  set F := ex (-P.ω (k + 1))
  set S := ex (-(2 * π / P.K))
  linear_combination ((1 - (τ : ℂ)) * (2 * (r : ℂ) * Complex.I * S + 4 * (P.ρ : ℂ) * r *
      (Complex.I * Complex.I) * S) + (τ : ℂ) * (2 * (r : ℂ) * Complex.I - 4 * (P.ρ : ℂ) * r *
      (Complex.I * Complex.I)) - 2 * (r : ℂ) * Complex.I) * hF
    + ((1 - (τ : ℂ)) * 4 * (P.ρ : ℂ) * r * S - 4 * (P.ρ : ℂ) * r * τ) * hI

theorem ex_neg_twist_mul_inv (hn : ‖P.n‖ = 1) (k : ℤ) :
    ex (-P.twist k) * P.n⁻¹ = -Complex.I * ex (-P.ω k) := by
  have hn0 : P.n ≠ 0 := by intro h; rw [h, norm_zero] at hn; norm_num at hn
  rw [ex_neg, ex_twist hn, ex_neg]
  unfold tangent
  have h1 : ex (P.ω k) ≠ 0 := ex_ne_zero _
  field_simp
  simp [Complex.I_sq]

 
theorem Good.four_rho_le_sin (hP : P.Good) : 4 * P.ρ ≤ Real.sin (2 * π / P.K) := by
  have hK := hP.K_pos
  have hθ0 : 0 ≤ 2 * π / P.K := by positivity
  have hθ : 2 * π / P.K ≤ π / 2 := by
    rw [div_le_iff₀ hK]; nlinarith [Real.pi_pos, hP.K_ge]
  have h1 := Real.mul_le_sin hθ0 hθ
  have h2 : 2 / π * (2 * π / P.K) = 4 / P.K := by field_simp; ring
  rw [h2] at h1
  have h3 : 4 * P.ρ ≤ 4 / P.K := by
    rw [le_div_iff₀ hK]; nlinarith [hP.ρK_le]
  linarith

theorem re_bracket_out (r ρ θ : ℝ) :
    (-((2 * r : ℝ) : ℂ) * Complex.I * ex θ - ((4 * ρ * r : ℝ) : ℂ) * ex θ + ((2 * r : ℝ) : ℂ) * Complex.I
      - ((4 * ρ * r : ℝ) : ℂ)).re = 2 * r * Real.sin θ - 4 * ρ * r * Real.cos θ - 4 * ρ * r := by
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, ex_re, ex_im]
  ring

theorem re_bracket_in (r ρ θ : ℝ) :
    (((2 * r : ℝ) : ℂ) * Complex.I * ex (-θ) - ((4 * ρ * r : ℝ) : ℂ) * ex (-θ) - ((2 * r : ℝ) : ℂ) * Complex.I
      - ((4 * ρ * r : ℝ) : ℂ)).re = 2 * r * Real.sin θ - 4 * ρ * r * Real.cos θ - 4 * ρ * r := by
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, ex_re, ex_im, Real.cos_neg, Real.sin_neg]
  ring

 

theorem corridor_frame_out (hP : P.Good) (hr : 0 < r) (k : ℤ) {y : ℂ}
    (hy : y ∈ segment ℝ (P.gatePlus r k) (P.gateMinus r (k + 1))) :
    P.frameInv r k y ∈ corrOutH (P.twist k) ∧ P.modMap r k (P.frameInv r k y) = y := by
  have hρr : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  refine ⟨?_, modMap_frameInv hP.n_ne hρr.ne' k y⟩
  rw [segment_eq_image'] at hy
  obtain ⟨τ, hτ, rfl⟩ := hy
  show 4 ≤ (ex (-P.twist k) * P.frameInv r k _).re
  have h := ex_neg_twist_mul_inv hP.n_norm k
  have e1 : ex (-P.twist k) * P.frameInv r k (P.gatePlus r k + τ • (P.gateMinus r (k + 1) - P.gatePlus r k))
      = ((P.ρ * r)⁻¹ : ℝ) * (-Complex.I * ex (-P.ω k) * (P.gatePlus r k +
        (τ : ℂ) * (P.gateMinus r (k + 1) - P.gatePlus r k) - P.site r k)) := by
    unfold frameInv
    rw [Complex.real_smul, Complex.ofReal_inv]
    linear_combination (((P.ρ * r : ℝ) : ℂ)⁻¹ * (P.gatePlus r k + (τ : ℂ) *
      (P.gateMinus r (k + 1) - P.gatePlus r k) - P.site r k)) * h
  rw [e1, corridor_rot_out hP.n_norm hP.K_ne, Complex.re_ofReal_mul, Complex.add_re,
    Complex.ofReal_re, Complex.re_ofReal_mul, re_bracket_out]
  have hs := hP.four_rho_le_sin
  have hc := Real.cos_le_one (2 * π / P.K)
  have h0 : 0 ≤ 2 * r * Real.sin (2 * π / P.K) - 4 * P.ρ * r * Real.cos (2 * π / P.K) - 4 * P.ρ * r := by
    nlinarith [hP.ρ_pos]
  rw [le_inv_mul_iff₀ hρr]
  nlinarith [hτ.1]

 
theorem corridor_frame_in (hP : P.Good) (hr : 0 < r) (k : ℤ) {y : ℂ}
    (hy : y ∈ segment ℝ (P.gatePlus r k) (P.gateMinus r (k + 1))) :
    P.frameInv r (k + 1) y ∈ corrInH (P.twist (k + 1)) ∧
      P.modMap r (k + 1) (P.frameInv r (k + 1) y) = y := by
  have hρr : 0 < P.ρ * r := mul_pos hP.ρ_pos hr
  refine ⟨?_, modMap_frameInv hP.n_ne hρr.ne' (k + 1) y⟩
  rw [segment_eq_image'] at hy
  obtain ⟨τ, hτ, rfl⟩ := hy
  show 4 ≤ -(ex (-P.twist (k + 1)) * P.frameInv r (k + 1) _).re
  have h := ex_neg_twist_mul_inv hP.n_norm (k + 1)
  have e1 : -(ex (-P.twist (k + 1)) * P.frameInv r (k + 1)
      (P.gatePlus r k + τ • (P.gateMinus r (k + 1) - P.gatePlus r k)))
      = ((P.ρ * r)⁻¹ : ℝ) * (Complex.I * ex (-P.ω (k + 1)) * (P.gatePlus r k +
        (τ : ℂ) * (P.gateMinus r (k + 1) - P.gatePlus r k) - P.site r (k + 1))) := by
    unfold frameInv
    rw [Complex.real_smul, Complex.ofReal_inv]
    linear_combination (-(((P.ρ * r : ℝ) : ℂ)⁻¹ * (P.gatePlus r k + (τ : ℂ) *
      (P.gateMinus r (k + 1) - P.gatePlus r k) - P.site r (k + 1)))) * h
  rw [← Complex.neg_re, e1, corridor_rot_in hP.n_norm hP.K_ne, Complex.re_ofReal_mul, Complex.add_re,
    Complex.ofReal_re, Complex.re_ofReal_mul, re_bracket_in]
  have hs := hP.four_rho_le_sin
  have hc := Real.cos_le_one (2 * π / P.K)
  have h0 : 0 ≤ 2 * r * Real.sin (2 * π / P.K) - 4 * P.ρ * r * Real.cos (2 * π / P.K) - 4 * P.ρ * r := by
    nlinarith [hP.ρ_pos]
  rw [le_inv_mul_iff₀ hρr]
  nlinarith [hτ.2]

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
