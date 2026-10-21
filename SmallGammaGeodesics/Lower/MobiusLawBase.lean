import SmallGammaGeodesics.Lower.Mobius
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Möbius maps of source §7: the algebra used by the law and drift statements (packet P-L2)

Source: `source/small-parameter-lqg-geodesics.pdf`, §7; planning audit GA4
(`planning/audits/GA4-sections-7-8.md`), "Details for later use", items **A1**, **A3**, **A4**.
Throughout `φ_θ = mobPhi θ`, `ψ_θ = mobPhi (-θ)`, and
`D_θ(z) = 1 + (e^{iθ} − 1) z` is the denominator of `φ_θ`. The definitions `mobPhi`, `rectU` and
the A1 lemmas (`hasDerivAt_mobPhi`, `mobPhi_neg_mobPhi`, `mobPhi_mobPhi_neg`, `injOn_mobPhi`,
`norm_exp_mul_I_sub_one_le`, `exp_neg_mul_I`) are those of packet P-L1 (`Lower/Mobius.lean`).

* `mobDen_mobPhi_neg`: `D_θ(ψ_θ z) = D_{−θ}(z)⁻¹` (the matrices of `φ_θ` and `ψ_θ` multiply to the
  identity);
* `norm_deriv_mobPhi`: `‖φ_θ′(z)‖ = ‖D_θ(z)‖⁻²`, and
  `norm_deriv_mobPhi_mobPhi_neg`: `‖φ_θ′(ψ_θ z)‖ ‖ψ_θ′(z)‖ = 1`;
* `norm_mobPhi_sub_mobPhi`: `|φ_θ(z) − φ_θ(w)| = |z − w| / (|D_θ(z)| |D_θ(w)|)` (the Möbius identity of
  GA4 A3, step 4; `ad − bc = e^{iθ}` has modulus one);
* `half_lt_norm_mobDen`: `‖D_θ(z)‖ > 1/2` for `|θ| ≤ 1/10` and `‖z‖ < 5`, so the poles stay away
  from `B₅(0)`; `injOn_mobPhi_neg_ball`, `differentiableAt_mobPhi_neg` on `B₅(0)`;
* `rectU_subset_ball`, `abs_le_tenth_of_abs_le`: the §7 data `U_R = rectU 100 R` (`R ≤ 10⁻³`) and
  `|θ| ≤ 64 R` satisfy these hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace SmallGammaGeodesics

/-! ### Algebra of `φ_θ` and `ψ_θ` -/

/-- `D_θ(ψ_θ z) = D_{−θ}(z)⁻¹`. -/
theorem mobDen_mobPhi_neg {θ : ℝ} {z : ℂ}
    (hz : 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0) :
    1 + (Complex.exp (θ * Complex.I) - 1) * mobPhi (-θ) z =
      (1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z)⁻¹ := by
  unfold mobPhi
  rw [exp_neg_mul_I] at hz ⊢
  set e := Complex.exp (θ * Complex.I) with he
  have he0 : e ≠ 0 := Complex.exp_ne_zero _
  refine eq_inv_of_mul_eq_one_left ?_
  rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ hz]
  have hee : e * e⁻¹ = 1 := mul_inv_cancel₀ he0
  linear_combination z * hee

/-- `ψ_θ` maps the complement of its pole into the complement of the pole of `φ_θ`. -/
theorem mobDen_mobPhi_neg_ne_zero {θ : ℝ} {z : ℂ}
    (hz : 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0) :
    1 + (Complex.exp (θ * Complex.I) - 1) * mobPhi (-θ) z ≠ 0 := by
  rw [mobDen_mobPhi_neg hz]
  exact inv_ne_zero hz

/-- `‖φ_θ′(z)‖ = ‖D_θ(z)‖⁻²`. -/
theorem norm_deriv_mobPhi {θ : ℝ} {z : ℂ} (hz : 1 + (Complex.exp (θ * Complex.I) - 1) * z ≠ 0) :
    ‖deriv (mobPhi θ) z‖ = (‖1 + (Complex.exp (θ * Complex.I) - 1) * z‖ ^ 2)⁻¹ := by
  rw [(hasDerivAt_mobPhi hz).deriv, norm_div, norm_pow, Complex.norm_exp_ofReal_mul_I, one_div]

/-- `φ_θ′(ψ_θ z) ψ_θ′(z) = 1`, in norm. -/
theorem norm_deriv_mobPhi_mobPhi_neg {θ : ℝ} {z : ℂ}
    (hz : 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0) :
    ‖deriv (mobPhi θ) (mobPhi (-θ) z)‖ * ‖deriv (mobPhi (-θ)) z‖ = 1 := by
  rw [norm_deriv_mobPhi (mobDen_mobPhi_neg_ne_zero hz), norm_deriv_mobPhi hz,
    mobDen_mobPhi_neg hz, norm_inv]
  have h0 : ‖1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  field_simp

/-- The Möbius difference identity (GA4 A3, step 4):
`φ_θ(z) − φ_θ(w) = e^{iθ} (z − w) / (D_θ(z) D_θ(w))`. -/
theorem mobPhi_sub_mobPhi {θ : ℝ} {z w : ℂ}
    (hz : 1 + (Complex.exp (θ * Complex.I) - 1) * z ≠ 0)
    (hw : 1 + (Complex.exp (θ * Complex.I) - 1) * w ≠ 0) :
    mobPhi θ z - mobPhi θ w = Complex.exp (θ * Complex.I) * (z - w) /
      ((1 + (Complex.exp (θ * Complex.I) - 1) * z) * (1 + (Complex.exp (θ * Complex.I) - 1) * w)) := by
  unfold mobPhi
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring

/-- `|φ_θ(z) − φ_θ(w)| = |z − w| / (|D_θ(z)| |D_θ(w)|)`. -/
theorem norm_mobPhi_sub_mobPhi {θ : ℝ} {z w : ℂ}
    (hz : 1 + (Complex.exp (θ * Complex.I) - 1) * z ≠ 0)
    (hw : 1 + (Complex.exp (θ * Complex.I) - 1) * w ≠ 0) :
    ‖mobPhi θ z - mobPhi θ w‖ = ‖z - w‖ /
      (‖1 + (Complex.exp (θ * Complex.I) - 1) * z‖ * ‖1 + (Complex.exp (θ * Complex.I) - 1) * w‖) := by
  rw [mobPhi_sub_mobPhi hz hw, norm_div, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    one_mul]

/-- `‖(e^{iθ} − 1) z‖ ≤ |θ| ‖z‖`. -/
theorem norm_mobC_mul_le (θ : ℝ) (z : ℂ) :
    ‖(Complex.exp (θ * Complex.I) - 1) * z‖ ≤ |θ| * ‖z‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_exp_mul_I_sub_one_le θ) (norm_nonneg z)

/-- `1 − ‖u‖ ≤ ‖1 + u‖`. -/
theorem one_sub_norm_le_norm_one_add (u : ℂ) : 1 - ‖u‖ ≤ ‖1 + u‖ := by
  have h := norm_sub_le (1 + u) u
  rw [add_sub_cancel_right, norm_one] at h
  linarith

/-- The denominators are bounded below on `B₅(0)` for `|θ| ≤ 1/10`: `‖D_θ(z)‖ > 1/2`. -/
theorem half_lt_norm_mobDen {θ : ℝ} {z : ℂ} (hθ : |θ| ≤ 1 / 10) (hz : ‖z‖ < 5) :
    1 / 2 < ‖1 + (Complex.exp (θ * Complex.I) - 1) * z‖ := by
  have h1 := norm_mobC_mul_le θ z
  have h2 : |θ| * ‖z‖ < 1 / 2 := by
    calc |θ| * ‖z‖ ≤ 1 / 10 * ‖z‖ := mul_le_mul_of_nonneg_right hθ (norm_nonneg z)
      _ < 1 / 10 * 5 := by linarith
      _ = 1 / 2 := by norm_num
  linarith [one_sub_norm_le_norm_one_add ((Complex.exp (θ * Complex.I) - 1) * z)]

/-- `D_θ(z) ≠ 0` on `B₅(0)` for `|θ| ≤ 1/10`. -/
theorem mobDen_ne_zero_of_mem_ball {θ : ℝ} {z : ℂ} (hθ : |θ| ≤ 1 / 10)
    (hz : z ∈ Metric.ball (0 : ℂ) 5) : 1 + (Complex.exp (θ * Complex.I) - 1) * z ≠ 0 := by
  rw [mem_ball_zero_iff] at hz
  intro h0
  have h := half_lt_norm_mobDen hθ hz
  rw [h0, norm_zero] at h
  linarith

/-- The same for `ψ_θ = mobPhi (-θ)`. -/
theorem mobDen_neg_ne_zero_of_mem_ball {θ : ℝ} {z : ℂ} (hθ : |θ| ≤ 1 / 10)
    (hz : z ∈ Metric.ball (0 : ℂ) 5) :
    1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0 :=
  mobDen_ne_zero_of_mem_ball (by rwa [abs_neg]) hz

/-- `ψ_θ` is injective on `B₅(0)` for `|θ| ≤ 1/10`. -/
theorem injOn_mobPhi_neg_ball {θ : ℝ} (hθ : |θ| ≤ 1 / 10) :
    Set.InjOn (mobPhi (-θ)) (Metric.ball (0 : ℂ) 5) :=
  (injOn_mobPhi (-θ)).mono fun _ hz => mobDen_neg_ne_zero_of_mem_ball hθ hz

/-- `ψ_θ` is complex differentiable on `B₅(0)` for `|θ| ≤ 1/10`. -/
theorem differentiableAt_mobPhi_neg {θ : ℝ} {z : ℂ} (hθ : |θ| ≤ 1 / 10)
    (hz : z ∈ Metric.ball (0 : ℂ) 5) : DifferentiableAt ℂ (mobPhi (-θ)) z :=
  (hasDerivAt_mobPhi (mobDen_neg_ne_zero_of_mem_ball hθ hz)).differentiableAt

/-! ### The §7 data satisfy the hypotheses -/

/-- `|θ| ≤ 64 R` and `R ≤ 10⁻³` give `|θ| ≤ 1/10`. -/
theorem abs_le_tenth_of_abs_le {R θ : ℝ} (hR1 : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R) :
    |θ| ≤ 1 / 10 := by
  linarith

/-- `U_R = rectU 100 R ⊆ B₅(0)` for `R ≤ 10⁻³`. -/
theorem rectU_subset_ball {R : ℝ} (hR1 : R ≤ 1 / 1000) : rectU 100 R ⊆ Metric.ball (0 : ℂ) 5 := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hz
  have hre : |z.re| ≤ 5 / 4 := abs_le.2 ⟨by linarith, h2.le⟩
  rw [mem_ball_zero_iff]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ < 5 := by linarith

end SmallGammaGeodesics
