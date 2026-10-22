import HigherDimLQGMetric.Gauss.GaussianHolderBasic
import Mathlib.Analysis.Convex.Integral

/-!
# The Gaussian Hölder inequality (D-GH), part 2: Mehler's formula (packet G2)

Source: planning audit `planning/audits/MA4-sections-7-10-appA.md`, Details (a) A7, Step 1
(the Ornstein–Uhlenbeck semigroup of [7] = Chen–Dafnis–Paouris, arXiv:1306.2410, §2.2).

We use the **angle parametrization** of the Ornstein–Uhlenbeck semigroup (`e^{-t} = cos φ`):
for `H : E → ℝ`,

  `mehler φ H x = ∫ H(cos φ • x + sin φ • y) dγ(y)`,

so that `mehler 0 H = H` and `mehler (π/2) H = ∫ H dγ`. For `H` with a bounded continuous gradient
`DH`, the map `(φ, x) ↦ mehler φ H x` is differentiable in both variables, with no singularity at
the endpoints (in contrast with the time parametrization of [7], whose `t`-derivative involves
`(1 - e^{-2t})^{-1/2}`):

* `hasFDerivAt_mehler`: the gradient in `x` is `cos φ • mehlerGrad φ DH x`, where
  `mehlerGrad φ DH x = ∫ DH(cos φ • x + sin φ • y) dγ(y)`;
* `hasDerivAt_mehler_angle`: the `φ`-derivative is
  `mehlerDeriv φ DH x = ∫ ⟪DH(cos φ • x + sin φ • y), -sin φ • x + cos φ • y⟫ dγ(y)`.

The key identity of the semigroup proof (`integral_mul_mehlerDeriv`, the Gaussian integration by
parts step of A7, Step 3) is, for every `Ψ` with bounded continuous gradient `DΨ`,

  `∫ Ψ(x) mehlerDeriv φ DH x dγ(x) = -sin φ ∫ ⟪mehlerGrad φ DH x, DΨ x⟫ dγ(x)`.

It is proved by rotating `(x, y) ↦ (cos φ • x + sin φ • y, -sin φ • x + cos φ • y)` (which
preserves `γ ⊗ γ`) and applying Stein's lemma in the second variable only; in particular no
second derivatives of `H` are needed (an addition to A7, which uses `L = Δ - x · ∇`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric.Gauss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Mehler's formula** for the Ornstein–Uhlenbeck semigroup at angle `φ` (`e^{-t} = cos φ`):
`mehler φ H x = ∫ H(cos φ • x + sin φ • y) dγ(y)`. -/
def mehler (φ : ℝ) (H : E → ℝ) (x : E) : ℝ :=
  ∫ y, H (cos φ • x + sin φ • y) ∂(stdGaussian E)

/-- The averaged gradient `∫ DH(cos φ • x + sin φ • y) dγ(y)`; the gradient of `mehler φ H` is
`cos φ • mehlerGrad φ DH`. -/
def mehlerGrad (φ : ℝ) (DH : E → E) (x : E) : E :=
  ∫ y, DH (cos φ • x + sin φ • y) ∂(stdGaussian E)

/-- The angle derivative `∂_φ mehler φ H x`. -/
def mehlerDeriv (φ : ℝ) (DH : E → E) (x : E) : ℝ :=
  ∫ y, ⟪DH (cos φ • x + sin φ • y), -sin φ • x + cos φ • y⟫ ∂(stdGaussian E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_affine_angle (φ : ℝ) (x : E) :
    Continuous fun y : E => cos φ • x + sin φ • y := by fun_prop

omit [BorelSpace E] in
lemma mehler_zero (H : E → ℝ) (x : E) : mehler 0 H x = H x := by
  simp [mehler]

omit [BorelSpace E] in
lemma mehler_pi_div_two (H : E → ℝ) (x : E) :
    mehler (π / 2) H x = ∫ y, H y ∂(stdGaussian E) := by
  simp [mehler]

lemma integrable_mehler_integrand {H : E → ℝ} (hc : Continuous H) {M : ℝ}
    (hM : ∀ z, |H z| ≤ M) (φ : ℝ) (x : E) :
    Integrable (fun y => H (cos φ • x + sin φ • y)) (stdGaussian E) :=
  integrable_of_continuous_of_bound (hc.comp (continuous_affine_angle φ x)) fun _ => hM _

lemma mehler_le {H : E → ℝ} (hc : Continuous H) {M : ℝ} (hM : ∀ z, |H z| ≤ M) {b : ℝ}
    (hb : ∀ z, H z ≤ b) (φ : ℝ) (x : E) : mehler φ H x ≤ b := by
  have h := integral_mono (integrable_mehler_integrand hc hM φ x)
    (integrable_const (μ := stdGaussian E) b) (fun y => hb (cos φ • x + sin φ • y))
  simpa [mehler] using h

lemma le_mehler {H : E → ℝ} (hc : Continuous H) {M : ℝ} (hM : ∀ z, |H z| ≤ M) {a : ℝ}
    (ha : ∀ z, a ≤ H z) (φ : ℝ) (x : E) : a ≤ mehler φ H x := by
  have h := integral_mono (integrable_const (μ := stdGaussian E) a)
    (integrable_mehler_integrand hc hM φ x) (fun y => ha (cos φ • x + sin φ • y))
  simpa [mehler] using h

section Grad

variable {DH : E → E} {C : ℝ}

lemma integrable_mehlerGrad_integrand (hc : Continuous DH) (hb : ∀ z, ‖DH z‖ ≤ C) (φ : ℝ)
    (x : E) : Integrable (fun y => DH (cos φ • x + sin φ • y)) (stdGaussian E) :=
  Integrable.of_bound (hc.comp (continuous_affine_angle φ x)).aestronglyMeasurable C
    (ae_of_all _ fun _ => hb _)

lemma continuous_mehlerGrad (hc : Continuous DH) (hb : ∀ z, ‖DH z‖ ≤ C) (φ : ℝ) :
    Continuous (mehlerGrad φ DH) :=
  continuous_of_dominated
    (fun x => (hc.comp (continuous_affine_angle φ x)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun y => hb (cos φ • x + sin φ • y)) (integrable_const C)
    (ae_of_all _ fun y => hc.comp (by fun_prop))

omit [BorelSpace E] in
lemma norm_mehlerGrad_le (hb : ∀ z, ‖DH z‖ ≤ C) (φ : ℝ) (x : E) :
    ‖mehlerGrad φ DH x‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := stdGaussian E)
    (ae_of_all _ fun y => hb (cos φ • x + sin φ • y))
  simpa [mehlerGrad] using h

lemma mehlerGrad_mem (hc : Continuous DH) (hb : ∀ z, ‖DH z‖ ≤ C) {S : Submodule ℝ E}
    (hS : ∀ z, DH z ∈ S) (φ : ℝ) (x : E) : mehlerGrad φ DH x ∈ S :=
  Convex.integral_mem S.convex S.closed_of_finiteDimensional
    (ae_of_all _ fun y => hS (cos φ • x + sin φ • y)) (integrable_mehlerGrad_integrand hc hb φ x)

end Grad

/-- The gradient of `mehler φ H` is `cos φ • mehlerGrad φ DH`. -/
theorem hasFDerivAt_mehler {H : E → ℝ} {DH : E → E} {C M : ℝ} (hH : HasBddGrad H DH C)
    (hM : ∀ z, |H z| ≤ M) (φ : ℝ) (x₀ : E) :
    HasFDerivAt (mehler φ H) (innerSL ℝ (cos φ • mehlerGrad φ DH x₀)) x₀ := by
  have hDH := integrable_mehlerGrad_integrand hH.continuous_grad hH.norm_grad_le φ x₀
  have hF' : Integrable (fun y => innerSL ℝ (cos φ • DH (cos φ • x₀ + sin φ • y)))
      (stdGaussian E) :=
    Integrable.of_bound ((innerSL ℝ).continuous.comp (continuous_const.smul
      (hH.continuous_grad.comp (continuous_affine_angle φ x₀)))).aestronglyMeasurable C
      (ae_of_all _ fun y => by
        rw [innerSL_apply_norm, norm_smul, Real.norm_eq_abs]
        exact (mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one φ)).trans
          (hH.norm_grad_le _))
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := stdGaussian E)
    (F := fun x y => H (cos φ • x + sin φ • y))
    (F' := fun x y => innerSL ℝ (cos φ • DH (cos φ • x + sin φ • y)))
    (x₀ := x₀) (bound := fun _ => C) (s := univ) univ_mem
    (Eventually.of_forall fun x =>
      (hH.continuous.comp (continuous_affine_angle φ x)).aestronglyMeasurable)
    (integrable_mehler_integrand hH.continuous hM φ x₀) hF'.aestronglyMeasurable
    (ae_of_all _ fun y x _ => by
      rw [innerSL_apply_norm, norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one φ)).trans
        (hH.norm_grad_le _))
    (integrable_const C)
    (ae_of_all _ fun y x _ => hasFDerivAt_comp_smul_add hH.hasFDerivAt (cos φ) (sin φ • y) x)
  refine key.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
  rw [ContinuousLinearMap.integral_apply hF' w]
  show ∫ y, ⟪cos φ • DH (cos φ • x₀ + sin φ • y), w⟫ ∂(stdGaussian E) =
    ⟪cos φ • mehlerGrad φ DH x₀, w⟫
  rw [mehlerGrad, ← integral_smul]
  simp_rw [real_inner_comm w]
  exact integral_inner (f := fun y => cos φ • DH (cos φ • x₀ + sin φ • y)) (hDH.smul (cos φ)) w

lemma continuous_mehler {H : E → ℝ} {DH : E → E} {C M : ℝ} (hH : HasBddGrad H DH C)
    (hM : ∀ z, |H z| ≤ M) (φ : ℝ) : Continuous (mehler φ H) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_mehler hH hM φ x).continuousAt

/-- The derivative of `mehler φ H x` with respect to the angle `φ`. -/
theorem hasDerivAt_mehler_angle {H : E → ℝ} {DH : E → E} {C M : ℝ} (hH : HasBddGrad H DH C)
    (hM : ∀ z, |H z| ≤ M) (x : E) (φ₀ : ℝ) :
    HasDerivAt (fun φ => mehler φ H x) (mehlerDeriv φ₀ DH x) φ₀ := by
  have hbound : ∀ (φ : ℝ) (y : E),
      ‖⟪DH (cos φ • x + sin φ • y), -sin φ • x + cos φ • y⟫‖ ≤ C * (‖x‖ + ‖y‖) := by
    intro φ y
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul (hH.norm_grad_le _) ?_ (norm_nonneg _)
      hH.nonneg)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, abs_neg]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one φ)
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one φ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := stdGaussian E)
    (F := fun φ y => H (cos φ • x + sin φ • y))
    (F' := fun φ y => ⟪DH (cos φ • x + sin φ • y), -sin φ • x + cos φ • y⟫)
    (x₀ := φ₀) (bound := fun y => C * (‖x‖ + ‖y‖)) (s := univ) univ_mem
    (Eventually.of_forall fun φ =>
      (hH.continuous.comp (continuous_affine_angle φ x)).aestronglyMeasurable)
    (integrable_mehler_integrand hH.continuous hM φ₀ x)
    ((hH.continuous_grad.comp (continuous_affine_angle φ₀ x)).inner
      (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun y φ _ => hbound φ y)
    (((integrable_const ‖x‖).add integrable_norm_stdGaussian).const_mul C)
    (ae_of_all _ fun y φ _ => by
      have h1 : HasDerivAt (fun φ : ℝ => cos φ • x + sin φ • y) (-sin φ • x + cos φ • y) φ :=
        ((hasDerivAt_cos φ).smul_const x).add ((hasDerivAt_sin φ).smul_const y)
      have h2 := (hH.hasFDerivAt (cos φ • x + sin φ • y)).comp_hasDerivAt φ h1
      simpa only [Function.comp_def, innerSL_apply_apply] using h2)
  exact key.2

section Deriv

variable {DH : E → E} {C : ℝ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_mehlerDeriv_integrand_le (hb : ∀ z, ‖DH z‖ ≤ C) (φ : ℝ) (x y : E) :
    ‖⟪DH (cos φ • x + sin φ • y), -sin φ • x + cos φ • y⟫‖ ≤ C * (‖x‖ + ‖y‖) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans (mul_le_mul (hb _) ?_ (norm_nonneg _) hC)
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_sin_le_one φ)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (abs_cos_le_one φ)

lemma integrable_mehlerDeriv_integrand (hc : Continuous DH) (hb : ∀ z, ‖DH z‖ ≤ C) (φ : ℝ)
    (x : E) :
    Integrable (fun y => ⟪DH (cos φ • x + sin φ • y), -sin φ • x + cos φ • y⟫)
      (stdGaussian E) :=
  (((integrable_const ‖x‖).add integrable_norm_stdGaussian).const_mul C).mono'
    ((hc.comp (continuous_affine_angle φ x)).inner (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun y => norm_mehlerDeriv_integrand_le hb φ x y)

lemma abs_mehlerDeriv_le (hb : ∀ z, ‖DH z‖ ≤ C) (φ : ℝ) (x : E) :
    |mehlerDeriv φ DH x| ≤ C * (‖x‖ + ∫ y, ‖y‖ ∂(stdGaussian E)) := by
  have hint := ((integrable_const ‖x‖).add (integrable_norm_stdGaussian (E := E))).const_mul C
  calc |mehlerDeriv φ DH x|
      ≤ ∫ y, C * (‖x‖ + ‖y‖) ∂(stdGaussian E) := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le hint
          (ae_of_all _ fun y => norm_mehlerDeriv_integrand_le hb φ x y)
    _ = C * (‖x‖ + ∫ y, ‖y‖ ∂(stdGaussian E)) := by
        rw [integral_const_mul, integral_add (integrable_const _) integrable_norm_stdGaussian]
        simp

lemma continuous_mehlerDeriv (hc : Continuous DH) (hb : ∀ z, ‖DH z‖ ≤ C) (φ : ℝ) :
    Continuous (mehlerDeriv φ DH) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  refine continuousAt_of_dominated (bound := fun y => C * ((‖x₀‖ + 1) + ‖y‖))
    (Eventually.of_forall fun x =>
      ((hc.comp (continuous_affine_angle φ x)).inner (by fun_prop)).aestronglyMeasurable)
    ?_ (((integrable_const _).add integrable_norm_stdGaussian).const_mul C)
    (ae_of_all _ fun y => (((hc.comp (by fun_prop)).inner (by fun_prop)).continuousAt :
      ContinuousAt (fun x : E => ⟪DH (cos φ • x + sin φ • y), -sin φ • x + cos φ • y⟫) x₀))
  filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
  refine ae_of_all _ fun y => (norm_mehlerDeriv_integrand_le hb φ x y).trans ?_
  have hC : 0 ≤ C := (norm_nonneg _).trans (hb 0)
  have : ‖x‖ ≤ ‖x₀‖ + 1 := by
    have h1 : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
      simpa using norm_add_le x₀ (x - x₀)
    have h2 : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hx
    linarith
  gcongr

end Deriv

/-- **The integration-by-parts identity of the semigroup proof** (MA4 A7, Step 3, in the angle
parametrization): for `Ψ` bounded with bounded continuous gradient `DΨ`,
`∫ Ψ(x) ∂_φ(mehler φ H)(x) dγ(x) = -sin φ ∫ ⟪mehlerGrad φ DH x, DΨ x⟫ dγ(x)`.

Proof: write the left side as an integral over `γ ⊗ γ`, rotate by `-φ` (which preserves `γ ⊗ γ`),
so that the integrand becomes `Ψ(cos φ • y - sin φ • v) ⟪DH y, v⟫`; apply Stein's lemma in `v`, and
rotate back. -/
theorem integral_mul_mehlerDeriv {DH : E → E} {C : ℝ} (hDHc : Continuous DH)
    (hDHb : ∀ z, ‖DH z‖ ≤ C) {Ψ : E → ℝ} {DΨ : E → E} {CΨ C' : ℝ} (hΨ : HasBddGrad Ψ DΨ C')
    (hΨb : ∀ z, |Ψ z| ≤ CΨ) (φ : ℝ) :
    ∫ x, Ψ x * mehlerDeriv φ DH x ∂(stdGaussian E) =
      -sin φ * ∫ x, ⟪mehlerGrad φ DH x, DΨ x⟫ ∂(stdGaussian E) := by
  set γ := stdGaussian E with hγ
  set μ := γ.prod γ with hμ
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hDHb 0)
  have hCΨ0 : 0 ≤ CΨ := (abs_nonneg _).trans (hΨb 0)
  have hC'0 : 0 ≤ C' := hΨ.nonneg
  have hΨc := hΨ.continuous
  have hDΨc := hΨ.continuous_grad
  have hR := measurePreserving_rotation (E := E) (-φ)
  have hR1 : ∀ q : E × E, (ContinuousLinearMap.rotation (-φ) q).1 = cos φ • q.1 + -sin φ • q.2 :=
    fun q => by rw [rotation_apply_fst, Real.cos_neg, Real.sin_neg]
  -- the integrand of the left side, on `E × E`
  set f : E × E → ℝ := fun p => Ψ p.1 *
    ⟪DH (cos φ • p.1 + sin φ • p.2), -sin φ • p.1 + cos φ • p.2⟫ with hf
  have hfc : Continuous f := hΨc.comp continuous_fst |>.mul
    ((hDHc.comp (by fun_prop)).inner (by fun_prop))
  have hf_int : Integrable f μ := by
    refine (integrable_norm_add_norm_prod.const_mul (CΨ * C)).mono' hfc.aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [hf, norm_mul, mul_assoc]
    exact mul_le_mul (by simpa [Real.norm_eq_abs] using hΨb p.1)
      (norm_mehlerDeriv_integrand_le hDHb φ p.1 p.2) (norm_nonneg _) hCΨ0
  -- the rotated integrand
  set g : E × E → ℝ := fun q => Ψ (cos φ • q.1 + -sin φ • q.2) * ⟪DH q.1, q.2⟫ with hg
  have hfg : ∀ q, f (ContinuousLinearMap.rotation (-φ) q) = g q := by
    intro q
    have h := rotation_rotation_neg φ q
    simp only [hf, hg]
    rw [← rotation_apply_fst φ (ContinuousLinearMap.rotation (-φ) q),
      ← rotation_apply_snd φ (ContinuousLinearMap.rotation (-φ) q), h, hR1]
  have hgc : Continuous g := (hΨc.comp (by fun_prop)).mul
    ((hDHc.comp continuous_fst).inner continuous_snd)
  have hg_int : Integrable g μ := by
    refine (integrable_norm_add_norm_prod.const_mul (CΨ * C)).mono' hgc.aestronglyMeasurable
      (ae_of_all _ fun q => ?_)
    simp only [hg, norm_mul, mul_assoc]
    refine mul_le_mul (by simpa [Real.norm_eq_abs] using hΨb _) ?_ (norm_nonneg _) hCΨ0
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    refine mul_le_mul (hDHb _) ?_ (norm_nonneg _) hC0
    linarith [norm_nonneg q.1]
  -- the integrand of the right side, on `E × E`, and its rotation
  set h : E × E → ℝ := fun p => ⟪DΨ p.1, DH (cos φ • p.1 + sin φ • p.2)⟫ with hh
  set k : E × E → ℝ := fun q => ⟪DΨ (cos φ • q.1 + -sin φ • q.2), DH q.1⟫ with hk
  have hhk : ∀ q, h (ContinuousLinearMap.rotation (-φ) q) = k q := by
    intro q
    have h' := rotation_rotation_neg φ q
    simp only [hh, hk]
    rw [← rotation_apply_fst φ (ContinuousLinearMap.rotation (-φ) q), h', hR1]
  have hhc : Continuous h := (hDΨc.comp continuous_fst).inner (hDHc.comp (by fun_prop))
  have hkc : Continuous k := (hDΨc.comp (by fun_prop)).inner (hDHc.comp continuous_fst)
  have hkb : ∀ q, ‖k q‖ ≤ C' * C := fun q => by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hΨ.norm_grad_le _) (hDHb _)
      (norm_nonneg _) hC'0)
  have hhb : ∀ p, ‖h p‖ ≤ C' * C := fun p => by
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hΨ.norm_grad_le _) (hDHb _)
      (norm_nonneg _) hC'0)
  have hk_int : Integrable k μ :=
    Integrable.of_bound hkc.aestronglyMeasurable (C' * C) (ae_of_all _ hkb)
  have hh_int : Integrable h μ :=
    Integrable.of_bound hhc.aestronglyMeasurable (C' * C) (ae_of_all _ hhb)
  -- Step 1: the left side as an integral over `γ ⊗ γ`
  have step1 : ∫ x, Ψ x * mehlerDeriv φ DH x ∂γ = ∫ p, f p ∂μ := by
    rw [integral_prod f hf_int]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [mehlerDeriv, hf]
    rw [integral_const_mul]
  -- Step 2: rotation by `-φ`
  have step2 : ∫ p, f p ∂μ = ∫ q, g q ∂μ := by
    have h2 := integral_map (μ := μ) hR.measurable.aemeasurable
      (hfc.aestronglyMeasurable (μ := μ.map (ContinuousLinearMap.rotation (-φ))))
    rw [hR.map_eq] at h2
    rw [h2]
    exact integral_congr_ae (ae_of_all _ fun q => hfg q)
  -- Step 3: Stein's lemma in the second variable
  have step3 : ∫ q, g q ∂μ = -sin φ * ∫ q, k q ∂μ := by
    rw [integral_prod g hg_int, integral_prod k hk_int, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have hG := hΨ.comp_add_smul (-sin φ) (cos φ • y)
    have hs := integral_inner_mul_eq_integral_inner_grad (C := CΨ) hG (fun z => hΨb _) (DH y)
    simp only [hg, hk]
    simp_rw [mul_comm (Ψ _) _]
    rw [hs]
    simp_rw [real_inner_smul_left]
    rw [integral_const_mul]
  -- Step 4: rotation back
  have step4 : ∫ q, k q ∂μ = ∫ p, h p ∂μ := by
    have h4 := integral_map (μ := μ) hR.measurable.aemeasurable
      (hhc.aestronglyMeasurable (μ := μ.map (ContinuousLinearMap.rotation (-φ))))
    rw [hR.map_eq] at h4
    rw [h4]
    exact integral_congr_ae (ae_of_all _ fun q => (hhk q).symm)
  -- Step 5: the right side
  have step5 : ∫ p, h p ∂μ = ∫ x, ⟪mehlerGrad φ DH x, DΨ x⟫ ∂γ := by
    rw [integral_prod h hh_int]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hh, mehlerGrad]
    rw [integral_inner (integrable_mehlerGrad_integrand hDHc hDHb φ x), real_inner_comm]
  rw [step1, step2, step3, step4, step5]

end HigherDimLQGMetric.Gauss
