import GaussianLQG.Probability.GaussianLp.Basic

/-!
# The finite-dimensional Gaussian `L^p` inequality (Maurey–Pisier)

Blueprint Proposition `prop:gaussian-Lp`, step "Finite dimensions". Let `φ : E → ℝ` be Lipschitz
on a finite-dimensional real inner product space and let `X, Y` be independent standard Gaussian
vectors. Then for `1 ≤ p < ∞`

  `‖φ(X) - E φ(X)‖_p ≤ c_p ‖ |∇φ(X)| ‖_p`,  `c_p = (π/2) (E|N|^p)^{1/p}`

(`lintegral_rpow_sub_integral_le`, `GaussianLQG.gaussian_Lp_inequality_finiteDim`), where `∇φ`
is the Fréchet derivative, which exists almost everywhere by Rademacher's theorem.

Proof (blueprint). Put `X_θ = sin θ X + cos θ Y`, `X'_θ = cos θ X - sin θ Y`, so that
`(X_θ, X'_θ) = rotPair θ (X, Y)` has the law of `(X, Y)`
(`LQGDimension.MaxConc.measurePreserving_rotPair`).

1. `θ ↦ φ(X_θ)` is Lipschitz, so (FTC for absolutely continuous functions)
   `φ(X) - φ(Y) = ∫_0^{π/2} (d/dθ) φ(X_θ) dθ`; by Fubini, for a.e. `(X, Y)` the point `X_θ` is a
   differentiability point of `φ` for a.e. `θ` (`X_θ` is standard Gaussian, hence has a density),
   and there `(d/dθ) φ(X_θ) = ∇φ(X_θ)(X'_θ)`.
2. Jensen on `[0, π/2]` (not Minkowski):
   `|φ(X) - φ(Y)|^p ≤ (π/2)^{p-1} ∫_0^{π/2} |∇φ(X_θ)(X'_θ)|^p dθ`.
3. Fubini and rotation invariance: `E|φ(X) - φ(Y)|^p ≤ (π/2)^p E|∇φ(X)(Y)|^p
   = (π/2)^p E|N|^p E‖∇φ(X)‖^p`, because `∇φ(X)(Y) ∼ 𝒩(0, ‖∇φ(X)‖²)` given `X`.
4. Jensen in `Y`: `E|φ(X) - E φ|^p ≤ E|φ(X) - φ(Y)|^p`.

The coordinate version `lintegral_rpow_sub_integral_le_gaussPi` (on `ℝⁿ = Fin n → ℝ` with the
product Gaussian measure, with the partial derivatives given as an a.e. hypothesis) is the form
used in the projection step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

namespace GaussLp

open LQGDimension.MaxConc (rotPair measurePreserving_rotPair)

section FiniteDim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rotation curve `θ ↦ sin θ • x + cos θ • y` has derivative `cos θ • x - sin θ • y`. -/
lemma hasDerivAt_rotPair_fst (z : E × E) (θ : ℝ) :
    HasDerivAt (fun s => (rotPair s z).1) (rotPair θ z).2 θ := by
  have h := ((Real.hasDerivAt_sin θ).smul_const z.1).add ((Real.hasDerivAt_cos θ).smul_const z.2)
  have e : (rotPair θ z).2 = Real.cos θ • z.1 + -Real.sin θ • z.2 := by
    simp only [rotPair, neg_smul, sub_eq_add_neg]
  rw [e]
  exact h

/-- The rotation curve is `(‖x‖ + ‖y‖)`-Lipschitz. -/
lemma lipschitzWith_rotPair_fst (z : E × E) :
    LipschitzWith (‖z.1‖₊ + ‖z.2‖₊) (fun s => (rotPair s z).1) := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun s => (hasDerivAt_rotPair_fst z s).differentiableAt) fun s => ?_
  rw [(hasDerivAt_rotPair_fst z s).deriv]
  have h1 : ‖Real.cos s • z.1‖ ≤ ‖z.1‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one s)
  have h2 : ‖Real.sin s • z.2‖ ≤ ‖z.2‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one s)
  rw [← NNReal.coe_le_coe, NNReal.coe_add, coe_nnnorm, coe_nnnorm, coe_nnnorm]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- **FTC along the rotation** for a Lipschitz function:
`φ x - φ y = ∫_0^{π/2} (d/dθ) φ(sin θ x + cos θ y) dθ`. -/
lemma sub_eq_integral_deriv_rot {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) (z : E × E) :
    φ z.1 - φ z.2 = ∫ θ in (0 : ℝ)..(Real.pi / 2), deriv (fun s => φ (rotPair s z).1) θ := by
  have hlip : LipschitzWith (K * (‖z.1‖₊ + ‖z.2‖₊)) (fun s => φ (rotPair s z).1) :=
    hφ.comp (lipschitzWith_rotPair_fst z)
  rw [(hlip.lipschitzOnWith (s := uIcc 0 (Real.pi / 2))).absolutelyContinuousOnInterval
    |>.integral_deriv_eq_sub]
  simp [rotPair, Real.sin_pi_div_two, Real.cos_pi_div_two]

/-- The derivative along the rotation, `∇φ(X_θ)(X'_θ)`. -/
def rotDeriv (φ : E → ℝ) (θ : ℝ) (z : E × E) : ℝ :=
  fderiv ℝ φ (rotPair θ z).1 (rotPair θ z).2

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_rotPair_fst_swap :
    Continuous fun q : (E × E) × ℝ => (rotPair q.2 q.1).1 := by
  unfold rotPair
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_rotPair_snd_swap :
    Continuous fun q : (E × E) × ℝ => (rotPair q.2 q.1).2 := by
  unfold rotPair
  fun_prop

lemma measurable_rotDeriv (φ : E → ℝ) : Measurable fun q : (E × E) × ℝ => rotDeriv φ q.2 q.1 :=
  ContinuousLinearMap.measurable_apply₂.comp
    (((measurable_fderiv ℝ φ).comp continuous_rotPair_fst_swap.measurable).prodMk
      continuous_rotPair_snd_swap.measurable)

/-- A Lipschitz function of a standard Gaussian vector is integrable. -/
theorem integrable_of_lipschitz {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    Integrable φ (stdGaussian E) := by
  refine Integrable.mono' ((integrable_const |φ 0|).add
    ((IsGaussian.integrable_id.norm).const_mul (K : ℝ))) hφ.continuous.aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have h1 := hφ.dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at h1
  rw [Real.norm_eq_abs]
  have h2 := abs_sub_abs_le_abs_sub (φ x) (φ 0)
  simp only [Pi.add_apply, id]
  linarith

/-- For a.e. `(x, y)`, the point `sin θ x + cos θ y` is a differentiability point of `φ` for
a.e. `θ ∈ (0, π/2]`. -/
lemma ae_ae_differentiableAt_rot {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∀ᵐ z ∂(stdGaussian E).prod (stdGaussian E),
      ∀ᵐ θ ∂(volume.restrict (Ioc (0 : ℝ) (Real.pi / 2))),
        DifferentiableAt ℝ φ (rotPair θ z).1 := by
  set μ := stdGaussian E
  have hS : MeasurableSet {x : E | DifferentiableAt ℝ φ x} := measurableSet_of_differentiableAt ℝ φ
  have h0 : ∀ᵐ x ∂μ, DifferentiableAt ℝ φ x := ae_differentiableAt_stdGaussian hφ
  have hfst : ∀ᵐ q ∂μ.prod μ, DifferentiableAt ℝ φ q.1 := by
    have hmap : (μ.prod μ).map Prod.fst = μ := by
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    rw [← hmap] at h0
    exact ae_of_ae_map measurable_fst.aemeasurable h0
  have h1 : ∀ θ : ℝ, ∀ᵐ z ∂μ.prod μ, DifferentiableAt ℝ φ (rotPair θ z).1 := by
    intro θ
    have hθ := measurePreserving_rotPair (E := E) θ
    have hfst' := hfst
    rw [← hθ.map_eq] at hfst'
    exact ae_of_ae_map hθ.measurable.aemeasurable hfst'
  have hmeas : MeasurableSet {q : (E × E) × ℝ | DifferentiableAt ℝ φ (rotPair q.2 q.1).1} :=
    hS.preimage continuous_rotPair_fst_swap.measurable
  exact (Measure.ae_ae_comm hmeas).2 (ae_of_all _ h1)

/-- **FTC along the rotation**, almost surely, with the derivative written as `∇φ(X_θ)(X'_θ)`. -/
lemma ae_sub_eq_setIntegral_rotDeriv {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) :
    ∀ᵐ z ∂(stdGaussian E).prod (stdGaussian E),
      φ z.1 - φ z.2 = ∫ θ in Ioc (0 : ℝ) (Real.pi / 2), rotDeriv φ θ z := by
  filter_upwards [ae_ae_differentiableAt_rot hφ] with z hz
  rw [sub_eq_integral_deriv_rot hφ z, intervalIntegral.integral_of_le (by positivity)]
  refine integral_congr_ae ?_
  filter_upwards [hz] with θ hθ
  exact (hθ.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_rotPair_fst z θ)).deriv

/-- **Jensen on `[0, π/2]`**: `|φ x - φ y|^p ≤ (π/2)^{p-1} ∫_0^{π/2} |∇φ(X_θ)(X'_θ)|^p dθ`. -/
lemma enorm_sub_rpow_le {φ : E → ℝ} {p : ℝ} (hp : 1 ≤ p) (z : E × E)
    (hz : φ z.1 - φ z.2 = ∫ θ in Ioc (0 : ℝ) (Real.pi / 2), rotDeriv φ θ z) :
    ‖φ z.1 - φ z.2‖ₑ ^ p ≤ ENNReal.ofReal (Real.pi / 2) ^ (p - 1) *
      ∫⁻ θ in Ioc (0 : ℝ) (Real.pi / 2), ‖rotDeriv φ θ z‖ₑ ^ p := by
  rw [hz]
  have hmeas : AEStronglyMeasurable (fun θ => rotDeriv φ θ z)
      (volume.restrict (Ioc (0 : ℝ) (Real.pi / 2))) :=
    ((measurable_rotDeriv φ).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have h := enorm_integral_rpow_le (ν := volume.restrict (Ioc (0 : ℝ) (Real.pi / 2))) hmeas hp
  rwa [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero] at h

/-- **Finite-dimensional Gaussian `L^p` inequality**, lower-integral form:
`E|φ(X) - E φ|^p ≤ (π/2)^p E|N|^p E‖∇φ(X)‖^p` for Lipschitz `φ` and `p ≥ 1`. -/
theorem lintegral_rpow_sub_integral_le {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) {p : ℝ}
    (hp : 1 ≤ p) :
    ∫⁻ x, ‖φ x - ∫ y, φ y ∂stdGaussian E‖ₑ ^ p ∂stdGaussian E ≤
      ENNReal.ofReal (Real.pi / 2) ^ p * (∫⁻ t, ‖t‖ₑ ^ p ∂gaussianReal 0 1) *
        ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ p ∂stdGaussian E := by
  set μ := stdGaussian E
  set c := ENNReal.ofReal (Real.pi / 2) with hc
  set M := ∫⁻ t, ‖t‖ₑ ^ p ∂gaussianReal 0 1
  have hp0 : 0 ≤ p := by linarith
  have hφc : Continuous φ := hφ.continuous
  have hφi : Integrable φ μ := integrable_of_lipschitz hφ
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  -- Step 1: Jensen in `y`.
  have step1 : ∫⁻ x, ‖φ x - ∫ y, φ y ∂μ‖ₑ ^ p ∂μ ≤ ∫⁻ z, ‖φ z.1 - φ z.2‖ₑ ^ p ∂μ.prod μ := by
    have hm : Measurable fun z : E × E => ‖φ z.1 - φ z.2‖ₑ ^ p :=
      ((hφc.comp continuous_fst).sub (hφc.comp continuous_snd)).measurable.enorm.pow_const p
    rw [lintegral_prod _ hm.aemeasurable]
    refine lintegral_mono fun x => ?_
    have e : φ x - ∫ y, φ y ∂μ = ∫ y, (φ x - φ y) ∂μ := by
      rw [integral_sub (integrable_const _) hφi, integral_const, probReal_univ, one_smul]
    rw [e]
    exact enorm_integral_rpow_le_of_prob (continuous_const.sub hφc).aestronglyMeasurable hp
  -- Step 2: FTC along the rotation and Jensen in `θ`.
  have step2 : ∫⁻ z, ‖φ z.1 - φ z.2‖ₑ ^ p ∂μ.prod μ ≤
      ∫⁻ z, c ^ (p - 1) * (∫⁻ θ in Ioc (0 : ℝ) (Real.pi / 2), ‖rotDeriv φ θ z‖ₑ ^ p) ∂μ.prod μ := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_sub_eq_setIntegral_rotDeriv hφ] with z hz
    exact enorm_sub_rpow_le hp z hz
  -- Step 3: Fubini and rotation invariance.
  have hH : Measurable fun q : E × E => ‖fderiv ℝ φ q.1 q.2‖ₑ ^ p :=
    (ContinuousLinearMap.measurable_apply₂.comp
      (((measurable_fderiv ℝ φ).comp measurable_fst).prodMk measurable_snd)).enorm.pow_const p
  have hrot : ∀ θ : ℝ, ∫⁻ z, ‖rotDeriv φ θ z‖ₑ ^ p ∂μ.prod μ =
      ∫⁻ q, ‖fderiv ℝ φ q.1 q.2‖ₑ ^ p ∂μ.prod μ := fun θ =>
    (measurePreserving_rotPair θ).lintegral_comp hH
  have step3 : ∫⁻ z, c ^ (p - 1) * (∫⁻ θ in Ioc (0 : ℝ) (Real.pi / 2),
      ‖rotDeriv φ θ z‖ₑ ^ p) ∂μ.prod μ = c ^ p * ∫⁻ q, ‖fderiv ℝ φ q.1 q.2‖ₑ ^ p ∂μ.prod μ := by
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hctop),
      lintegral_lintegral_swap ((measurable_rotDeriv φ).enorm.pow_const p).aemeasurable]
    simp only [hrot]
    have hcp : c ^ (p - 1) * c = c ^ p := by
      have h := ENNReal.rpow_add (p - 1) 1 hc0 hctop
      rw [sub_add_cancel, ENNReal.rpow_one] at h
      exact h.symm
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← hc, mul_comm _ c, ← mul_assoc, hcp]
  -- Step 4: the conditional law of `∇φ(X)(Y)` given `X`.
  have step4 : ∫⁻ q, ‖fderiv ℝ φ q.1 q.2‖ₑ ^ p ∂μ.prod μ =
      M * ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ p ∂μ := by
    rw [lintegral_prod _ hH.aemeasurable]
    have h : ∀ x, ∫⁻ y, ‖fderiv ℝ φ x y‖ₑ ^ p ∂μ = ‖fderiv ℝ φ x‖ₑ ^ p * M := fun x =>
      lintegral_enorm_rpow_stdGaussian _ hp0
    simp only [h]
    rw [lintegral_mul_const _ ((measurable_fderiv ℝ φ).enorm.pow_const p), mul_comm]
  calc ∫⁻ x, ‖φ x - ∫ y, φ y ∂μ‖ₑ ^ p ∂μ
      ≤ ∫⁻ z, ‖φ z.1 - φ z.2‖ₑ ^ p ∂μ.prod μ := step1
    _ ≤ _ := step2
    _ = c ^ p * (M * ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ p ∂μ) := by rw [step3, step4]
    _ = c ^ p * M * ∫⁻ x, ‖fderiv ℝ φ x‖ₑ ^ p ∂μ := (mul_assoc _ _ _).symm

/-- Taking `p`-th roots of `A ≤ (π/2)^p M B`. -/
lemma rpow_inv_le_of_le {A M B : ℝ≥0∞} {p : ℝ} (hp : 0 < p)
    (h : A ≤ ENNReal.ofReal (Real.pi / 2) ^ p * M * B) :
    A ^ (1 / p) ≤ ENNReal.ofReal (Real.pi / 2) * M ^ (1 / p) * B ^ (1 / p) := by
  have h1p : 0 ≤ 1 / p := by positivity
  calc A ^ (1 / p) ≤ (ENNReal.ofReal (Real.pi / 2) ^ p * M * B) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h h1p
    _ = ENNReal.ofReal (Real.pi / 2) * M ^ (1 / p) * B ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h1p, ENNReal.mul_rpow_of_nonneg _ _ h1p,
          ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end FiniteDim

/-! ### The coordinate form on `ℝⁿ` -/

section Coordinates

/-- `ofReal r ^ p = ofReal (r²) ^ (p/2)` for `r ≥ 0`. -/
lemma ofReal_rpow_eq_ofReal_sq_rpow {r : ℝ} (hr : 0 ≤ r) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal r ^ p = ENNReal.ofReal (r ^ 2) ^ (p / 2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hr hp, ENNReal.ofReal_rpow_of_nonneg (by positivity)
    (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hr]
  congr 2
  push_cast
  ring

/-- **Finite-dimensional Gaussian `L^p` inequality in coordinates**: for Lipschitz
`φ : ℝⁿ → ℝ` whose partial derivatives are a.e. given by `d i`, under the product Gaussian measure,
`E|φ - E φ|^p ≤ (π/2)^p E|N|^p E (∑_i (d i)²)^{p/2}`. -/
theorem lintegral_rpow_sub_integral_le_gaussPi {n : ℕ} {φ : (Fin n → ℝ) → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) {p : ℝ} (hp : 1 ≤ p) {d : Fin n → (Fin n → ℝ) → ℝ}
    (hd : ∀ᵐ x ∂gaussPi n, ∀ i, HasDerivAt (fun t : ℝ => φ (x + t • Pi.single i 1)) (d i x) 0) :
    ∫⁻ x, ‖φ x - ∫ y, φ y ∂gaussPi n‖ₑ ^ p ∂gaussPi n ≤
      ENNReal.ofReal (Real.pi / 2) ^ p * (∫⁻ t, ‖t‖ₑ ^ p ∂gaussianReal 0 1) *
        ∫⁻ x, ENNReal.ofReal (∑ i, d i x ^ 2) ^ (p / 2) ∂gaussPi n := by
  set e := EuclideanSpace.equiv (Fin n) ℝ
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ := φ ∘ e with hψdef
  have hp0 : 0 ≤ p := by linarith
  have he : ∀ w, e w = WithLp.ofLp w := fun w => rfl
  have hψ : LipschitzWith K ψ := by
    have h := hφ.comp (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ))
    rw [mul_one] at h
    exact h
  have hψx : ∀ x : Fin n → ℝ, ψ (WithLp.toLp 2 x) = φ x := fun x => rfl
  have hmap : (gaussPi n).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ (Fin n)) :=
    map_pi_eq_stdGaussian
  have htoLp : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (PiLp.continuous_toLp 2 _).measurable
  -- transport of the mean
  have hmean : ∫ y, φ y ∂gaussPi n = ∫ w, ψ w ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    rw [← hmap, integral_map htoLp.aemeasurable hψ.continuous.aestronglyMeasurable]
    simp only [hψx]
  -- transport of the left side
  have hlhs : ∫⁻ x, ‖φ x - ∫ y, φ y ∂gaussPi n‖ₑ ^ p ∂gaussPi n =
      ∫⁻ w, ‖ψ w - ∫ w', ψ w' ∂stdGaussian (EuclideanSpace ℝ (Fin n))‖ₑ ^ p
        ∂stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    rw [← hmean, ← hmap, lintegral_map (f := fun w => ‖ψ w - ∫ y, φ y ∂gaussPi n‖ₑ ^ p)
      ((hψ.continuous.sub continuous_const).measurable.enorm.pow_const p) htoLp]
    simp only [hψx]
  -- the gradient in coordinates
  have hgrad : ∀ᵐ x ∂gaussPi n, ‖fderiv ℝ ψ (WithLp.toLp 2 x)‖ₑ ^ p =
      ENNReal.ofReal (∑ i, d i x ^ 2) ^ (p / 2) := by
    filter_upwards [ae_differentiableAt_gaussPi hφ, hd] with x hx hdx
    have hcomp : fderiv ℝ ψ (WithLp.toLp 2 x) = (fderiv ℝ φ x).comp (e : _ →L[ℝ] _) := by
      rw [hψdef, e.comp_right_fderiv]
      rfl
    have hcoord : ∀ i, fderiv ℝ ψ (WithLp.toLp 2 x) (EuclideanSpace.basisFun (Fin n) ℝ i) =
        d i x := by
      intro i
      rw [hcomp, EuclideanSpace.basisFun_apply, ContinuousLinearMap.comp_apply]
      have hline : HasDerivAt (fun t : ℝ => x + t • Pi.single i (1 : ℝ)) (Pi.single i 1) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ))).const_add x
      have h1 : HasDerivAt (fun t : ℝ => φ (x + t • Pi.single i 1))
          (fderiv ℝ φ x (Pi.single i 1)) 0 := by
        have hx0 : x + (0 : ℝ) • Pi.single i (1 : ℝ) = x := by simp
        have hx' : HasFDerivAt φ (fderiv ℝ φ x) (x + (0 : ℝ) • Pi.single i (1 : ℝ)) := by
          rw [hx0]
          exact hx.hasFDerivAt
        exact hx'.comp_hasDerivAt (0 : ℝ) hline
      exact h1.unique (hdx i)
    have hnorm : ‖fderiv ℝ ψ (WithLp.toLp 2 x)‖ ^ 2 = ∑ i, d i x ^ 2 := by
      rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_dual]
      simp only [hcoord]
    rw [← ofReal_norm, ofReal_rpow_eq_ofReal_sq_rpow (norm_nonneg _) hp0, hnorm]
  -- transport of the right side
  have hrhs : ∫⁻ w, ‖fderiv ℝ ψ w‖ₑ ^ p ∂stdGaussian (EuclideanSpace ℝ (Fin n)) =
      ∫⁻ x, ENNReal.ofReal (∑ i, d i x ^ 2) ^ (p / 2) ∂gaussPi n := by
    rw [← hmap, lintegral_map ((measurable_fderiv ℝ ψ).enorm.pow_const p) htoLp]
    exact lintegral_congr_ae hgrad
  rw [hlhs, ← hrhs]
  exact lintegral_rpow_sub_integral_le hψ hp

end Coordinates

end GaussLp

open GaussLp

/-- **Finite-dimensional Gaussian `L^p` inequality** (Maurey–Pisier; blueprint Proposition
`prop:gaussian-Lp`, step "Finite dimensions"): for a Lipschitz function `φ` on a
finite-dimensional real inner product space and `1 ≤ p < ∞`,
`‖φ - E φ‖_p ≤ c_p ‖ ‖∇φ‖ ‖_p` under the standard Gaussian measure, with
`c_p = (π/2) (E|N|^p)^{1/p}` and `∇φ = fderiv ℝ φ` (which exists a.e. by Rademacher's theorem). -/
theorem gaussian_Lp_inequality_finiteDim {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {φ : E → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => φ x - ∫ y, φ y ∂stdGaussian E) (ENNReal.ofReal p) (stdGaussian E) ≤
      ENNReal.ofReal (Real.pi / 2 * (∫ x, |x| ^ p ∂gaussianReal 0 1) ^ (1 / p)) *
        eLpNorm (fun x => ‖fderiv ℝ φ x‖) (ENNReal.ofReal p) (stdGaussian E) := by
  have hp0 : 0 < p := by linarith
  have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
  change _ ≤ ENNReal.ofReal (gaussLpConst p) * _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp0.le, ofReal_gaussLpConst hp0]
  simp only [enorm_norm]
  exact rpow_inv_le_of_le hp0 (lintegral_rpow_sub_integral_le hφ hp)

end GaussianLQG
