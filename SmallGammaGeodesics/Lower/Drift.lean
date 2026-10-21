import SmallGammaGeodesics.Lower.MobiusLawBase
import QuantumZipper.Proofs.GFF.K3.Conformal
import LQGMetric.Field.Green
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The bending drift and its Dirichlet energy, source (7.4) (packet P-L2 T2)

Source: `source/small-parameter-lqg-geodesics.pdf`, §7, (7.4); corrected in planning audit GA4
(`planning/audits/GA4-sections-7-8.md`), "Details for later use", item **A4**.

For `0 < R ≤ 10⁻³`, `|θ| ≤ 64 R` and `Q ≥ 0`, the drift is
`g(z) = Q η(Re z) χ₀(Im z/(100R)) ℓ_θ(z)` with `ℓ_θ = log |ψ_θ′| = −log |D_{−θ}|²` (`bendLog`),
`η = 1` on `[−1/4, 5/4]` with support `[−1/2, 3/2]` (`driftEta`), and `χ₀ = 1` on `[−1, 1]` with
support `[−2, 2]` (`driftChi`). Then (`exists_bendingDrift`):

* `g` is a test function, equal to `Q log |ψ_θ′|` on `U_R = rectU 100 R`;
* `tsupport g ⊆ S_R = [−1/2, 3/2] × [−200R, 200R]`;
* `‖g‖²_∇ ≤ C_g Q² R³` with a numerical `C_g`.

Bounds on `S_R` (GA4 A4, steps 2–5, with slightly different numerical constants):
`|ℓ_θ| ≤ 2·10⁵ R²` (`abs_bendLog_le`), `|∇ℓ_θ| ≤ 256 R`, `|∇(η χ₀)| ≤ C_η + C_χ/(100R)`, hence
`|∇g| ≤ Q R (256 + 200 C_η + 2000 C_χ)` (`norm_fderiv_bendDriftFun_le`), and `|S_R| = 800 R`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace SmallGammaGeodesics

open LQGMetric

/-- The horizontal cutoff `η`: `1` on `[−1/4, 5/4]`, `tsupport η = [−1/2, 3/2]`. -/
def driftEta : ContDiffBump (1 / 2 : ℝ) := ⟨3 / 4, 1, by norm_num, by norm_num⟩

/-- The vertical cutoff `χ₀`: `1` on `[−1, 1]`, `tsupport χ₀ = [−2, 2]`. -/
def driftChi : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

/-- `ℓ_θ(z) = −log |1 + (e^{−iθ} − 1) z|²`, which is `log |ψ_θ′(z)|` off the pole (`bendLog_eq`). -/
def bendLog (θ : ℝ) (z : ℂ) : ℝ :=
  -Real.log (‖1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z‖ ^ 2)

/-- The cutoff `η(Re z) χ₀(Im z / (100 R))`. -/
def bendCut (R : ℝ) (z : ℂ) : ℝ := driftEta z.re * driftChi ((100 * R)⁻¹ * z.im)

/-- The bending drift `g = Q η(Re z) χ₀(Im z/(100R)) log |ψ_θ′(z)|` (source (7.4)). -/
def bendDriftFun (Q R θ : ℝ) (z : ℂ) : ℝ := Q * (bendCut R z * bendLog θ z)

/-- The closed rectangle `S_R = [−1/2, 3/2] × [−200R, 200R]`. -/
def bendRect (R : ℝ) : Set ℂ := {z | -1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2 ∧ |z.im| ≤ 200 * R}

/-! ### Elementary facts -/

theorem log_le_four_mul_abs_sub_one {x : ℝ} (hx : 1 / 4 ≤ x) : |Real.log x| ≤ 4 * |x - 1| := by
  have hx0 : 0 < x := by linarith
  have h1 : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos hx0
  have h2 : 1 - x⁻¹ ≤ Real.log x := Real.one_sub_inv_le_log_of_pos hx0
  rw [abs_le]
  constructor
  · rcases le_total 1 x with h | h
    · have : 0 ≤ Real.log x := Real.log_nonneg h
      have : 0 ≤ |x - 1| := abs_nonneg _
      linarith
    · have hinv : x⁻¹ ≤ 4 := by
        rw [inv_le_comm₀ hx0 (by norm_num)]
        linarith
      have hxx : 1 - x⁻¹ = -(1 - x) * x⁻¹ := by field_simp; ring
      rw [abs_of_nonpos (by linarith : x - 1 ≤ 0)]
      have : -(1 - x) * x⁻¹ ≥ -(1 - x) * 4 := by
        have : 0 ≤ 1 - x := by linarith
        nlinarith
      linarith
  · have : x - 1 ≤ |x - 1| := le_abs_self _
    have : 0 ≤ |x - 1| := abs_nonneg _
    linarith

theorem mem_bendRect_norm_le {R : ℝ} (hR1 : R ≤ 1 / 1000) {z : ℂ} (hz : z ∈ bendRect R) :
    ‖z‖ ≤ 2 := by
  obtain ⟨h1, h2, h3⟩ := hz
  have hre : |z.re| ≤ 3 / 2 := abs_le.2 ⟨by linarith, h2⟩
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 3 / 2 + 200 * R := add_le_add hre h3
    _ ≤ 2 := by linarith

theorem isCompact_bendRect (R : ℝ) (hR1 : R ≤ 1 / 1000) : IsCompact (bendRect R) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have e : bendRect R = {z : ℂ | -1 / 2 ≤ z.re} ∩ {z : ℂ | z.re ≤ 3 / 2} ∩
        {z : ℂ | |z.im| ≤ 200 * R} := by
      ext z
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    rw [e]
    exact ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz => ?_
    rw [mem_closedBall_zero_iff]
    exact mem_bendRect_norm_le hR1 hz

theorem mem_ball_of_mem_bendRect {R : ℝ} (hR1 : R ≤ 1 / 1000) {z : ℂ} (hz : z ∈ bendRect R) :
    z ∈ Metric.ball (0 : ℂ) 5 := by
  rw [mem_ball_zero_iff]
  linarith [mem_bendRect_norm_le hR1 hz]

/-- `ℓ_θ = log |ψ_θ′|` off the pole of `ψ_θ`. -/
theorem bendLog_eq {θ : ℝ} {z : ℂ}
    (hz : 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0) :
    bendLog θ z = Real.log ‖deriv (mobPhi (-θ)) z‖ := by
  rw [norm_deriv_mobPhi hz, Real.log_inv, bendLog]

theorem driftEta_eq_one {x : ℝ} (h1 : -1 / 4 < x) (h2 : x < 5 / 4) : driftEta x = 1 := by
  refine driftEta.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  exact ⟨by simp only [driftEta]; linarith, by simp only [driftEta]; linarith⟩

theorem driftChi_eq_one {y : ℝ} (hy : |y| ≤ 1) : driftChi y = 1 := by
  refine driftChi.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact hy

theorem driftEta_eq_zero {x : ℝ} (hx : ¬ (-1 / 2 ≤ x ∧ x ≤ 3 / 2)) : driftEta x = 0 := by
  refine image_eq_zero_of_notMem_tsupport ?_
  rw [driftEta.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le]
  simp only [driftEta]
  intro h
  exact hx ⟨by linarith [h.1], by linarith [h.2]⟩

theorem driftChi_eq_zero {y : ℝ} (hy : 2 < |y|) : driftChi y = 0 := by
  refine image_eq_zero_of_notMem_tsupport ?_
  rw [driftChi.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, sub_zero]
  simp only [driftChi]
  linarith

theorem bendCut_nonneg (R : ℝ) (z : ℂ) : 0 ≤ bendCut R z :=
  mul_nonneg driftEta.nonneg driftChi.nonneg

theorem bendCut_le_one (R : ℝ) (z : ℂ) : bendCut R z ≤ 1 := by
  calc bendCut R z ≤ 1 * 1 :=
        mul_le_mul driftEta.le_one driftChi.le_one driftChi.nonneg zero_le_one
    _ = 1 := one_mul 1

theorem bendCut_eq_one {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ rectU 100 R) : bendCut R z = 1 := by
  obtain ⟨h1, h2, h3⟩ := hz
  rw [bendCut, driftEta_eq_one h1 h2, driftChi_eq_one, one_mul]
  rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 100 * R)]
  rw [inv_mul_le_iff₀ (by positivity : (0 : ℝ) < 100 * R)]
  linarith

theorem bendCut_eq_zero {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∉ bendRect R) : bendCut R z = 0 := by
  have hz' : ¬ (-1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2 ∧ |z.im| ≤ 200 * R) := hz
  rw [not_and_or, not_and_or] at hz'
  rcases hz' with h | h | h
  · rw [bendCut, driftEta_eq_zero fun h' => h h'.1, zero_mul]
  · rw [bendCut, driftEta_eq_zero fun h' => h h'.2, zero_mul]
  · rw [bendCut, driftChi_eq_zero, mul_zero]
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 100 * R)]
    rw [lt_inv_mul_iff₀ (by positivity : (0 : ℝ) < 100 * R)]
    linarith

theorem bendDriftFun_eq_zero {Q R θ : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∉ bendRect R) :
    bendDriftFun Q R θ z = 0 := by
  rw [bendDriftFun, bendCut_eq_zero hR hz, zero_mul, mul_zero]

/-! ### Smoothness -/

theorem contDiff_bendCut (R : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bendCut R) :=
  (driftEta.contDiff.comp Complex.reCLM.contDiff).mul
    (driftChi.contDiff.comp (contDiff_const.mul Complex.imCLM.contDiff))

theorem contDiffOn_bendLog (θ : ℝ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bendLog θ)
      {z | 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0} := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => ‖1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  exact (h.contDiffOn.log fun z hz => pow_ne_zero 2 (norm_ne_zero_iff.2 hz)).neg

theorem bendRect_subset_mobDen_ne {R θ : ℝ} (hR1 : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R) :
    bendRect R ⊆ {z | 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0} := fun _ hz =>
  mobDen_neg_ne_zero_of_mem_ball (abs_le_tenth_of_abs_le hR1 hθ) (mem_ball_of_mem_bendRect hR1 hz)

theorem contDiff_bendDriftFun {Q R θ : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 1000)
    (hθ : |θ| ≤ 64 * R) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bendDriftFun Q R θ) := by
  have hO : IsOpen {z : ℂ | 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  refine QuantumZipper.K3.contDiff_of_contDiffOn_of_support_subset hO
    (isCompact_bendRect R hR1) (bendRect_subset_mobDen_ne hR1 hθ) ?_
    fun z hz => bendDriftFun_eq_zero hR hz
  exact contDiffOn_const.mul ((contDiff_bendCut R).contDiffOn.mul (contDiffOn_bendLog θ))

theorem tsupport_bendDriftFun_subset {Q R θ : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 1000) :
    tsupport (bendDriftFun Q R θ) ⊆ bendRect R :=
  closure_minimal (fun _ hz => by_contra fun h => hz (bendDriftFun_eq_zero hR h))
    (isCompact_bendRect R hR1).isClosed

/-- The bending drift as a test function. -/
def bendDrift (Q R θ : ℝ) (hR : 0 < R) (hR1 : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R) : TestC where
  toFun := bendDriftFun Q R θ
  contDiff' := contDiff_bendDriftFun hR hR1 hθ
  hasCompactSupport' := HasCompactSupport.intro (isCompact_bendRect R hR1) fun _ hz =>
    bendDriftFun_eq_zero hR hz
  tsupport_subset' := Set.subset_univ _

/-! ### Pointwise bounds on `S_R` -/

/-- `|ℓ_θ| ≤ 2·10⁵ R²` on `S_R` (GA4 A4, step 2). -/
theorem abs_bendLog_le {R θ : ℝ} (hR : 0 < R) (hR1 : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R) {z : ℂ}
    (hz : z ∈ bendRect R) : |bendLog θ z| ≤ 200000 * R ^ 2 := by
  set u : ℂ := (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z with hu
  have hzn : ‖z‖ ≤ 2 := mem_bendRect_norm_le hR1 hz
  obtain ⟨hz1, hz2, hz3⟩ := hz
  have hre : |z.re| ≤ 3 / 2 := abs_le.2 ⟨by linarith, hz2⟩
  -- `N = ‖1 + u‖² = 1 + 2 Re u + ‖u‖²`
  have hN : ‖1 + u‖ ^ 2 = 1 + 2 * u.re + ‖u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    ring
  -- `Re u = (cos θ − 1) Re z + sin θ Im z`
  have hure : u.re = (Real.cos θ - 1) * z.re + Real.sin θ * z.im := by
    rw [hu, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg, Real.sin_neg]
    ring
  have hθ2 : θ ^ 2 ≤ (64 * R) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  have hcos : |Real.cos θ - 1| ≤ θ ^ 2 / 2 := by
    rw [abs_of_nonpos (by linarith [Real.cos_le_one θ])]
    linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hsin : |Real.sin θ| ≤ 64 * R := Real.abs_sin_le_abs.trans hθ
  have hure_le : |u.re| ≤ 15872 * R ^ 2 := by
    rw [hure]
    calc |(Real.cos θ - 1) * z.re + Real.sin θ * z.im|
        ≤ |Real.cos θ - 1| * |z.re| + |Real.sin θ| * |z.im| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (64 * R) ^ 2 / 2 * (3 / 2) + 64 * R * (200 * R) := by
          gcongr
          · linarith
      _ = 15872 * R ^ 2 := by ring
  have hun : ‖u‖ ≤ 128 * R := by
    calc ‖u‖ ≤ |(-θ : ℝ)| * ‖z‖ := norm_mobC_mul_le (-θ) z
      _ ≤ 64 * R * 2 := by
          rw [abs_neg]
          exact mul_le_mul hθ hzn (norm_nonneg z) (by positivity)
      _ = 128 * R := by ring
  have hun2 : ‖u‖ ^ 2 ≤ 16384 * R ^ 2 := by
    calc ‖u‖ ^ 2 ≤ (128 * R) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hun 2
      _ = 16384 * R ^ 2 := by ring
  have hN1 : |‖1 + u‖ ^ 2 - 1| ≤ 48128 * R ^ 2 := by
    rw [hN, show 1 + 2 * u.re + ‖u‖ ^ 2 - 1 = 2 * u.re + ‖u‖ ^ 2 by ring]
    calc |2 * u.re + ‖u‖ ^ 2| ≤ |2 * u.re| + |‖u‖ ^ 2| := abs_add_le _ _
      _ = 2 * |u.re| + ‖u‖ ^ 2 := by
          rw [abs_mul, abs_two, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖u‖ ^ 2)]
      _ ≤ 2 * (15872 * R ^ 2) + 16384 * R ^ 2 := by linarith
      _ = 48128 * R ^ 2 := by ring
  have hhalf : 1 / 2 < ‖1 + u‖ :=
    half_lt_norm_mobDen (abs_le_tenth_of_abs_le hR1 (by rwa [abs_neg])) (by linarith)
  have hquarter : 1 / 4 ≤ ‖1 + u‖ ^ 2 := by nlinarith
  rw [bendLog, abs_neg]
  calc |Real.log (‖1 + u‖ ^ 2)| ≤ 4 * |‖1 + u‖ ^ 2 - 1| := log_le_four_mul_abs_sub_one hquarter
    _ ≤ 4 * (48128 * R ^ 2) := by linarith
    _ ≤ 200000 * R ^ 2 := by nlinarith

/-! ### Derivatives on `S_R` -/

/-- The derivative of the cutoff `η(Re z) χ₀(Im z/(100R))`. -/
theorem hasFDerivAt_bendCut (R : ℝ) (z : ℂ) :
    HasFDerivAt (bendCut R)
      (driftEta z.re • (deriv driftChi ((100 * R)⁻¹ * z.im) • ((100 * R)⁻¹ • Complex.imCLM)) +
        driftChi ((100 * R)⁻¹ * z.im) • (deriv driftEta z.re • Complex.reCLM)) z := by
  have hη : HasFDerivAt (fun z : ℂ => driftEta z.re) (deriv driftEta z.re • Complex.reCLM) z := by
    have hd : HasDerivAt driftEta (deriv driftEta z.re) z.re :=
      ((driftEta.contDiff (n := 1)).differentiable one_ne_zero z.re).hasDerivAt
    exact hd.comp_hasFDerivAt z Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun z : ℂ => (100 * R)⁻¹ * z.im) ((100 * R)⁻¹ • Complex.imCLM) z :=
    Complex.imCLM.hasFDerivAt.const_mul ((100 * R)⁻¹)
  have hχ : HasFDerivAt (fun z : ℂ => driftChi ((100 * R)⁻¹ * z.im))
      (deriv driftChi ((100 * R)⁻¹ * z.im) • ((100 * R)⁻¹ • Complex.imCLM)) z := by
    have hd : HasDerivAt driftChi (deriv driftChi ((100 * R)⁻¹ * z.im)) ((100 * R)⁻¹ * z.im) :=
      ((driftChi.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    exact HasDerivAt.comp_hasFDerivAt (h₂ := (driftChi : ℝ → ℝ))
      (f := fun z : ℂ => (100 * R)⁻¹ * z.im) z hd him
  exact hη.mul hχ

theorem abs_driftEta_le_one (x : ℝ) : |driftEta x| ≤ 1 := by
  rw [abs_of_nonneg driftEta.nonneg]; exact driftEta.le_one

theorem abs_driftChi_le_one (y : ℝ) : |driftChi y| ≤ 1 := by
  rw [abs_of_nonneg driftChi.nonneg]; exact driftChi.le_one

/-- `|∇(η χ₀)| ≤ C_χ/(100R) + C_η`. -/
theorem norm_fderiv_bendCut_le {R Cη Cχ : ℝ} (hR : 0 < R)
    (hη : ∀ x, ‖deriv driftEta x‖ ≤ Cη) (hχ : ∀ x, ‖deriv driftChi x‖ ≤ Cχ) (z : ℂ) :
    ‖fderiv ℝ (bendCut R) z‖ ≤ Cχ * (100 * R)⁻¹ + Cη := by
  rw [(hasFDerivAt_bendCut R z).fderiv]
  have hR' : 0 < (100 * R)⁻¹ := by positivity
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, norm_smul, norm_smul, Complex.imCLM_norm, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs (100 * R)⁻¹, abs_of_pos hR']
    calc |driftEta z.re| * (‖deriv driftChi ((100 * R)⁻¹ * z.im)‖ * (100 * R)⁻¹)
        ≤ 1 * (Cχ * (100 * R)⁻¹) := by
          gcongr
          · exact abs_driftEta_le_one _
          · exact hχ _
      _ = Cχ * (100 * R)⁻¹ := one_mul _
  · rw [norm_smul, norm_smul, Complex.reCLM_norm, mul_one, Real.norm_eq_abs]
    calc |driftChi ((100 * R)⁻¹ * z.im)| * ‖deriv driftEta z.re‖ ≤ 1 * Cη := by
          gcongr
          · exact abs_driftChi_le_one _
          · exact hη _
      _ = Cη := one_mul _

/-- The derivative of `ℓ_θ = −log |D_{−θ}|²` off the pole. -/
theorem hasFDerivAt_bendLog {θ : ℝ} {z : ℂ}
    (hz : 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0) :
    HasFDerivAt (bendLog θ)
      (-((‖1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z‖ ^ 2)⁻¹ •
        (2 • (innerSL ℝ (1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z)).comp
          ((Complex.exp ((-θ : ℝ) * Complex.I) - 1) • ContinuousLinearMap.id ℝ ℂ)))) z := by
  have hu : HasFDerivAt (fun z : ℂ => 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z)
      ((Complex.exp ((-θ : ℝ) * Complex.I) - 1) • ContinuousLinearMap.id ℝ ℂ) z :=
    ((hasFDerivAt_id z).const_mul _).const_add 1
  exact ((hu.norm_sq).log (pow_ne_zero 2 (norm_ne_zero_iff.2 hz))).neg

/-- `|∇ℓ_θ| ≤ 2 |e^{−iθ} − 1| / |D_{−θ}|`. -/
theorem norm_fderiv_bendLog_le {θ : ℝ} {z : ℂ}
    (hz : 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z ≠ 0) :
    ‖fderiv ℝ (bendLog θ) z‖ ≤ 2 * ‖Complex.exp ((-θ : ℝ) * Complex.I) - 1‖ /
      ‖1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z‖ := by
  rw [(hasFDerivAt_bendLog hz).fderiv]
  set u := 1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z with hu
  set ε := Complex.exp ((-θ : ℝ) * Complex.I) - 1
  have hu0 : 0 < ‖u‖ := norm_pos_iff.2 hz
  rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ‖(2 • (innerSL ℝ u).comp (ε • ContinuousLinearMap.id ℝ ℂ) : ℂ →L[ℝ] ℝ)‖ ≤
      2 * (‖u‖ * ‖ε‖) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    rw [two_nsmul]
    change ‖innerSL ℝ u (ε • v) + innerSL ℝ u (ε • v)‖ ≤ _
    rw [innerSL_apply_apply, Real.norm_eq_abs, ← two_mul, abs_mul, abs_two]
    have h := abs_real_inner_le_norm u (ε • v)
    rw [norm_smul] at h
    nlinarith [abs_nonneg (inner ℝ u (ε • v)), norm_nonneg u, norm_nonneg ε, norm_nonneg v]
  calc (‖u‖ ^ 2)⁻¹ * ‖(2 • (innerSL ℝ u).comp (ε • ContinuousLinearMap.id ℝ ℂ) : ℂ →L[ℝ] ℝ)‖
      ≤ (‖u‖ ^ 2)⁻¹ * (2 * (‖u‖ * ‖ε‖)) := by gcongr
    _ = 2 * ‖ε‖ / ‖u‖ := by field_simp

/-- `|∇g| ≤ Q R (256 + 200 C_η + 2000 C_χ)` on `S_R` (GA4 A4, steps 3–4). -/
theorem norm_fderiv_bendDriftFun_le {Q R θ Cη Cχ : ℝ} (hQ : 0 ≤ Q) (hR : 0 < R)
    (hR1 : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R) (hCη : 0 ≤ Cη)
    (hη : ∀ x, ‖deriv driftEta x‖ ≤ Cη) (hχ : ∀ x, ‖deriv driftChi x‖ ≤ Cχ) {z : ℂ}
    (hz : z ∈ bendRect R) :
    ‖fderiv ℝ (bendDriftFun Q R θ) z‖ ≤ Q * R * (256 + 200 * Cη + 2000 * Cχ) := by
  have hD := bendRect_subset_mobDen_ne hR1 hθ hz
  have hcut : HasFDerivAt (bendCut R) (fderiv ℝ (bendCut R) z) z :=
    (hasFDerivAt_bendCut R z).differentiableAt.hasFDerivAt
  have hlog : HasFDerivAt (bendLog θ) (fderiv ℝ (bendLog θ) z) z :=
    (hasFDerivAt_bendLog hD).differentiableAt.hasFDerivAt
  have hg : HasFDerivAt (bendDriftFun Q R θ)
      (Q • (bendCut R z • fderiv ℝ (bendLog θ) z + bendLog θ z • fderiv ℝ (bendCut R) z)) z :=
    (hcut.mul hlog).const_mul Q
  rw [hg.fderiv]
  -- the two factors
  have hL : ‖fderiv ℝ (bendLog θ) z‖ ≤ 256 * R := by
    refine (norm_fderiv_bendLog_le hD).trans ?_
    have hhalf : 1 / 2 < ‖1 + (Complex.exp ((-θ : ℝ) * Complex.I) - 1) * z‖ :=
      half_lt_norm_mobDen (abs_le_tenth_of_abs_le hR1 (by rwa [abs_neg]))
        (by linarith [mem_bendRect_norm_le hR1 hz])
    have hε : ‖Complex.exp ((-θ : ℝ) * Complex.I) - 1‖ ≤ 64 * R := by
      refine (norm_exp_mul_I_sub_one_le (-θ)).trans ?_
      rwa [abs_neg]
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hC := norm_fderiv_bendCut_le hR hη hχ z
  have hℓ := abs_bendLog_le hR hR1 hθ hz
  have hc1 : |bendCut R z| ≤ 1 := by
    rw [abs_of_nonneg (bendCut_nonneg R z)]; exact bendCut_le_one R z
  calc ‖Q • (bendCut R z • fderiv ℝ (bendLog θ) z + bendLog θ z • fderiv ℝ (bendCut R) z)‖
      ≤ Q * (|bendCut R z| * ‖fderiv ℝ (bendLog θ) z‖ +
          |bendLog θ z| * ‖fderiv ℝ (bendCut R) z‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hQ]
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ Q * (1 * (256 * R) + 200000 * R ^ 2 * (Cχ * (100 * R)⁻¹ + Cη)) := by
        gcongr
    _ ≤ Q * R * (256 + 200 * Cη + 2000 * Cχ) := by
        have hRR : 200000 * R ^ 2 * (Cχ * (100 * R)⁻¹ + Cη) =
            R * (2000 * Cχ + 200000 * R * Cη) := by
          field_simp
          ring
        rw [hRR]
        have h1 : 200000 * R * Cη ≤ 200 * Cη := by nlinarith
        have h2 : Q * (R * (200000 * R * Cη)) ≤ Q * (R * (200 * Cη)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hR.le) hQ
        calc Q * (1 * (256 * R) + R * (2000 * Cχ + 200000 * R * Cη))
            = Q * (256 * R + R * (2000 * Cχ)) + Q * (R * (200000 * R * Cη)) := by ring
          _ ≤ Q * (256 * R + R * (2000 * Cχ)) + Q * (R * (200 * Cη)) := by linarith
          _ = Q * R * (256 + 200 * Cη + 2000 * Cχ) := by ring

/-- `|S_R| = 800 R`. -/
theorem volume_real_bendRect {R : ℝ} (hR : 0 < R) : volume.real (bendRect R) = 800 * R := by
  have hset : bendRect R = Complex.measurableEquivRealProd ⁻¹'
      (Icc (-1 / 2 : ℝ) (3 / 2) ×ˢ Icc (-(200 * R)) (200 * R)) := by
    ext z
    simp only [bendRect, mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Icc,
      abs_le]
    exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  have hvol : volume (bendRect R) = ENNReal.ofReal 2 * ENNReal.ofReal (400 * R) := by
    rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    congr 2 <;> ring
  rw [measureReal_def, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- **The bending cost (7.4)** (GA4 A4, step 5): `‖g‖²_∇ ≤ 800 (256 + 200 C_η + 2000 C_χ)² Q² R³`. -/
theorem gradEnergy_bendDriftFun_le {Q R θ Cη Cχ : ℝ} (hQ : 0 ≤ Q) (hR : 0 < R)
    (hR1 : R ≤ 1 / 1000) (hθ : |θ| ≤ 64 * R) (hCη : 0 ≤ Cη) (hCχ : 0 ≤ Cχ)
    (hη : ∀ x, ‖deriv driftEta x‖ ≤ Cη) (hχ : ∀ x, ‖deriv driftChi x‖ ≤ Cχ) :
    gradEnergy (bendDriftFun Q R θ) ≤ 800 * (256 + 200 * Cη + 2000 * Cχ) ^ 2 * Q ^ 2 * R ^ 3 := by
  set M : ℝ := Q * R * (256 + 200 * Cη + 2000 * Cχ) with hM
  have hM0 : 0 ≤ M := by positivity
  have hmeas : MeasurableSet (bendRect R) := (isCompact_bendRect R hR1).isClosed.measurableSet
  have hpt : ∀ z, ‖fderiv ℝ (bendDriftFun Q R θ) z‖ ^ 2 ≤
      (bendRect R).indicator (fun _ => M ^ 2) z := by
    intro z
    by_cases hz : z ∈ bendRect R
    · rw [indicator_of_mem hz]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_fderiv_bendDriftFun_le hQ hR hR1 hθ hCη hη hχ hz) 2
    · rw [indicator_of_notMem hz, fderiv_of_notMem_tsupport ℝ
        (fun h => hz (tsupport_bendDriftFun_subset hR hR1 h)), norm_zero]
      norm_num
  have hint : Integrable ((bendRect R).indicator fun _ => M ^ 2) :=
    (integrable_indicator_iff hmeas).2
      (integrableOn_const (isCompact_bendRect R hR1).measure_lt_top.ne)
  have hI := integral_mono_of_nonneg (ae_of_all _ fun z => sq_nonneg _) hint (ae_of_all _ hpt)
  rw [integral_indicator_const _ hmeas, volume_real_bendRect hR, smul_eq_mul] at hI
  have hπ : (2 * Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Real.two_le_pi])
  have hI0 : 0 ≤ ∫ z, ‖fderiv ℝ (bendDriftFun Q R θ) z‖ ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  unfold gradEnergy
  calc (2 * Real.pi)⁻¹ * ∫ z, ‖fderiv ℝ (bendDriftFun Q R θ) z‖ ^ 2
      ≤ 1 * (800 * R * M ^ 2) := by
        gcongr
    _ = 800 * (256 + 200 * Cη + 2000 * Cχ) ^ 2 * Q ^ 2 * R ^ 3 := by
        rw [hM]
        ring

/-- **The bending drift (7.4)** (GA4 A4, packet P-L2 T2). There is a numerical `C_g` such that for
`Q ≥ 0`, `0 < R ≤ 10⁻³` and `|θ| ≤ 64 R` there is a test function `g` with `g = Q log |ψ_θ′|` on
`U_R = rectU 100 R`, `tsupport g ⊆ [−1/2, 3/2] × [−200R, 200R]` and `‖g‖²_∇ ≤ C_g Q² R³`. -/
theorem exists_bendingDrift : ∃ Cg : ℝ, 0 < Cg ∧ ∀ Q : ℝ, 0 ≤ Q → ∀ R θ : ℝ, 0 < R →
    R ≤ 1 / 1000 → |θ| ≤ 64 * R → ∃ g : LQGMetric.TestC,
      (∀ z ∈ rectU 100 R, g z = Q * Real.log ‖deriv (mobPhi (-θ)) z‖) ∧
      tsupport (⇑g) ⊆ {z : ℂ | -1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2 ∧ |z.im| ≤ 200 * R} ∧
      LQGMetric.gradEnergy ⇑g ≤ Cg * Q ^ 2 * R ^ 3 := by
  obtain ⟨Cη, hη⟩ := ((driftEta.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
    driftEta.hasCompactSupport.deriv
  obtain ⟨Cχ, hχ⟩ := ((driftChi.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
    driftChi.hasCompactSupport.deriv
  have hCη : 0 ≤ Cη := (norm_nonneg _).trans (hη 0)
  have hCχ : 0 ≤ Cχ := (norm_nonneg _).trans (hχ 0)
  refine ⟨800 * (256 + 200 * Cη + 2000 * Cχ) ^ 2, by positivity,
    fun Q hQ R θ hR hR1 hθ => ⟨bendDrift Q R θ hR hR1 hθ, fun z hz => ?_,
      tsupport_bendDriftFun_subset hR hR1,
      gradEnergy_bendDriftFun_le hQ hR hR1 hθ hCη hCχ hη hχ⟩⟩
  show bendDriftFun Q R θ z = _
  rw [bendDriftFun, bendCut_eq_one hR hz, one_mul, bendLog_eq
    (mobDen_neg_ne_zero_of_mem_ball (abs_le_tenth_of_abs_le hR1 hθ) (rectU_subset_ball hR1 hz))]

end SmallGammaGeodesics
