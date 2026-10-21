import SmallGammaGeodesics.Upper.Coupling42Path
import LQGMetric.Field.MarkovWeylInt

/-!
# Pairings of a whole-plane GFF with regular measures (packet P-U1, `lem:pairing-limits` (a))

Blueprint `lem:pairing-limits` (a) in its general form, for **every** whole-plane GFF `g` and every
regular measure `μ` (finite, compactly supported, with a Hölder ball-mass bound
`μ(B_r(u)) ≤ C r^α`): almost surely the mollified pairings `X_n = ∫ ⟨g, ψ_{n,x}⟩ dμ(x)` converge,
and their limit is `measPairing g μ` (`ae_tendsto_measPairing_of_isWholePlaneGFF`). Consequently,
a.s. for every constant `c`, `(g + c, μ) = (g, μ) + c μ(ℂ)`
(`ae_measPairing_addConst_of_isWholePlaneGFF`).

This generalizes P-G3's path-measure argument (`Coupling42.ae_tendsto_bumpPath`) to arbitrary
regular measures. No realization argument is used.

* The radial retraction `ballRetract R` of `ℂ` onto `B̄(0, max R 1)` makes `x ↦ ψ_{n, r(x)}` a
  continuous family in the fixed space `𝓓_{B̄(0, max R 1 + 1)}`, bounded in each seminorm
  (`continuous_bumpK`, `bound_bumpK`). LQGMetric's `MarkovWeyl.exists_testIntegral_measure` then
  produces the test function `bumpMeas n μ R = ∫ ψ_{n, r(x)} dμ(x)`, with
  `T(bumpMeas n μ R) = ∫ T(ψ_{n, r(x)}) dμ(x)` for every distribution `T`. If `μ` lives on
  `B̄(0, R)`, then `r(x) = x` `μ`-a.e. (`pairing_bumpMeas`).
* As a measure, `bumpMeas n μ R dx = moll n μ = μ * ψ_n` (`withDensity_bumpMeas`); its mass is
  `μ(ℂ)` (`integral_bumpMeas`).
* With the Hölder bound of the logarithmic potential `U_μ` (GaussianLQG `integral_abs_log_sub_le`,
  through P-G3's `abs_integral_neg_log_moll_sub_le`, exponent `s = min (α/2) 1`), the potential of
  `bumpMeas n μ R` is within `H 2^{-ns}` of `U_μ`, so the mean-zero increment
  `D_n = bumpMeas (n+1) μ R − bumpMeas n μ R` has `logCov D_n D_n ≤ 4 μ(ℂ) H q^n`, `q = 2^{-s}`
  (`logCov_bumpMeasDiff_le`). Since `E ⟨g, D_n⟩² = logCov D_n D_n` for every whole-plane GFF
  (`CircleAvg.integral_sq_pair`), the increments are summable a.s.
  (`CircleAvg.ae_tendsto_of_sq_incr_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal Distributions BoundedContinuousFunction

namespace SmallGammaGeodesics

namespace MeasPair

open LQGMetric GaussianLQG GaussianLQG.Realization Coupling42

/-! ## The radial retraction onto a closed ball -/

/-- the radius `max R 1 > 0` -/
def rad (R : ℝ) : ℝ := max R 1

theorem rad_pos (R : ℝ) : 0 < rad R := lt_max_of_lt_right one_pos

theorem le_rad (R : ℝ) : R ≤ rad R := le_max_left _ _

/-- the radial retraction `x ↦ (ρ / max ρ ‖x‖) x` of `ℂ` onto `B̄(0, ρ)`, `ρ = max R 1` -/
def ballRetract (R : ℝ) (x : ℂ) : ℂ := ((rad R / max (rad R) ‖x‖ : ℝ) : ℂ) * x

theorem continuous_ballRetract (R : ℝ) : Continuous (ballRetract R) := by
  unfold ballRetract
  refine Continuous.mul (Complex.continuous_ofReal.comp ?_) continuous_id
  exact continuous_const.div (continuous_const.max continuous_norm)
    fun x => (lt_max_of_lt_left (rad_pos R)).ne'

theorem norm_ballRetract_le (R : ℝ) (x : ℂ) : ‖ballRetract R x‖ ≤ rad R := by
  unfold ballRetract
  have hρ := rad_pos R
  have hM : 0 < max (rad R) ‖x‖ := lt_max_of_lt_left hρ
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hρ.le hM.le),
    div_mul_eq_mul_div, div_le_iff₀ hM]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hρ.le

theorem ballRetract_of_norm_le {R : ℝ} {x : ℂ} (hx : ‖x‖ ≤ R) : ballRetract R x = x := by
  unfold ballRetract
  rw [max_eq_left (hx.trans (le_rad R)), div_self (rad_pos R).ne', Complex.ofReal_one, one_mul]

/-! ## The family `x ↦ ψ_{n, r(x)}` in a fixed `𝓓_K` -/

/-- the compact `B̄(0, max R 1 + 1)` -/
def ballK1 (R : ℝ) : TopologicalSpace.Compacts ℂ :=
  ⟨closedBall 0 (rad R + 1), isCompact_closedBall _ _⟩

theorem support_bumpTest_retract (n : ℕ) (R : ℝ) (x : ℂ) :
    Function.support (bumpTest n (ballRetract R x)) ⊆ (ballK1 R : Set ℂ) := by
  intro y hy
  by_contra hK
  apply hy
  apply CircleAvg.bumpTest_eq_zero
  have h1 : rad R + 1 < dist y 0 := by simpa [ballK1] using hK
  have h2 := norm_ballRetract_le R x
  have h3 := dist_triangle y (ballRetract R x) 0
  have h4 : dist (ballRetract R x) 0 = ‖ballRetract R x‖ := dist_zero_right _
  linarith

/-- `x ↦ ψ_{n, r(x)}` as a family in `𝓓_{B̄(0, max R 1 + 1)}` -/
def bumpK (n : ℕ) (R : ℝ) (x : ℂ) : 𝓓^{⊤}_{ballK1 R}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset (bumpTest n (ballRetract R x)).contDiff
    (support_bumpTest_retract n R x)

theorem bumpK_eq (n : ℕ) (R : ℝ) (x : ℂ) :
    TestFunction.ofSupportedIn (subset_univ _) (bumpK n R x) = bumpTest n (ballRetract R x) := by
  ext y; rfl

theorem structureMap_bumpK_apply (n : ℕ) (R : ℝ) (i : ℕ) (x y : ℂ) :
    (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (bumpK n R x)) y =
      iteratedFDeriv ℝ i (bumpTest n 0 : ℂ → ℝ) (y - ballRetract R x) := by
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact CircleAvg.iteratedFDeriv_bumpTest n _ i y

theorem continuous_bumpK (n : ℕ) (R : ℝ) : Continuous (bumpK n R) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  set G := iteratedFDeriv ℝ i (bumpTest n 0 : ℂ → ℝ)
  have hGc : Continuous G := (bumpTest n 0).contDiff.continuous_iteratedFDeriv
    (by exact_mod_cast le_top)
  have hGu : UniformContinuous G :=
    ((bumpTest n 0).hasCompactSupport.iteratedFDeriv i).uniformContinuous_of_continuous hGc
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  obtain ⟨δ, hδ, hG⟩ := Metric.uniformContinuous_iff.mp hGu (ε / 2) (by positivity)
  obtain ⟨η, hη, hc⟩ := Metric.continuous_iff.mp (continuous_ballRetract R) x₀ δ hδ
  refine ⟨η, hη, fun x hx => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).mpr fun y => ?_)
    (half_lt_self hε)
  simp only [Function.comp_apply, structureMap_bumpK_apply]
  refine (hG ?_).le
  rw [dist_eq_norm, sub_sub_sub_cancel_left, ← dist_eq_norm']
  exact hc x hx

theorem bound_bumpK (n : ℕ) (R : ℝ) (i : ℕ) :
    ∃ B, ∀ x, ‖ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (bumpK n R x)‖ ≤ B := by
  set G := iteratedFDeriv ℝ i (bumpTest n 0 : ℂ → ℝ)
  have hGc : Continuous G := (bumpTest n 0).contDiff.continuous_iteratedFDeriv
    (by exact_mod_cast le_top)
  obtain ⟨B, hB⟩ := hGc.bounded_above_of_compact_support
    ((bumpTest n 0).hasCompactSupport.iteratedFDeriv i)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B, fun x => (BoundedContinuousFunction.norm_le hB0).2 fun y => ?_⟩
  rw [structureMap_bumpK_apply]
  exact hB _

/-! ## The test function `bumpMeas n μ R = ∫ ψ_{n, r(x)} dμ(x)` -/

section bumpMeas

variable (n : ℕ) (μ : Measure ℂ) [IsFiniteMeasure μ] (R : ℝ)

theorem exists_bumpMeas :
    ∃ I : 𝓓^{⊤}_{ballK1 R}(ℂ, ℝ), (∀ y, I y = ∫ x, bumpK n R x y ∂μ) ∧
      ∀ T : 𝓓^{⊤}_{ballK1 R}(ℂ, ℝ) →L[ℝ] ℝ, T I = ∫ x, T (bumpK n R x) ∂μ :=
  MarkovWeyl.exists_testIntegral_measure μ (continuous_bumpK n R) (bound_bumpK n R)

/-- `∫ ψ_{n, r(x)} dμ(x)` as a test function (`r` the radial retraction onto `B̄(0, max R 1)`) -/
def bumpMeas : TestC :=
  TestFunction.ofSupportedIn (subset_univ _) (exists_bumpMeas n μ R).choose

theorem bumpMeas_apply' (y : ℂ) :
    bumpMeas n μ R y = ∫ x, bumpTest n (ballRetract R x) y ∂μ :=
  (exists_bumpMeas n μ R).choose_spec.1 y

/-- **Distributions commute with the integral**: `T(bumpMeas n μ R) = ∫ T(ψ_{n, r(x)}) dμ(x)`. -/
theorem pairing_bumpMeas' (T : DistC) :
    T (bumpMeas n μ R) = ∫ x, T (bumpTest n (ballRetract R x)) ∂μ := by
  have h := (exists_bumpMeas n μ R).choose_spec.2
    (T.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _)))
  have e1 : T (bumpMeas n μ R) =
      (T.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _))) (exists_bumpMeas n μ R).choose :=
    rfl
  rw [e1, h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show T (TestFunction.ofSupportedIn (subset_univ _) (bumpK n R x)) = _
  rw [bumpK_eq]

theorem bumpMeas_nonneg (y : ℂ) : 0 ≤ bumpMeas n μ R y := by
  rw [bumpMeas_apply']
  exact integral_nonneg fun x => CircleAvg.bumpTest_nonneg n _ y

theorem integrable_bumpMeas : Integrable (bumpMeas n μ R) :=
  (bumpMeas n μ R).continuous.integrable_of_hasCompactSupport (bumpMeas n μ R).hasCompactSupport

theorem integral_bumpMeas_mul' (f : ℂ → ℝ) (hf : Continuous f) :
    ∫ y, bumpMeas n μ R y * f y = ∫ x, (∫ y, bumpTest n (ballRetract R x) y * f y) ∂μ := by
  have hloc : LocallyIntegrableOn f ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) volume := by
    rw [TopologicalSpace.Opens.coe_top, locallyIntegrableOn_univ]
    exact hf.locallyIntegrable
  set T : DistC := Distribution.ofFun ⊤ f volume ⊤ with hT
  have hTapp : ∀ φ : TestC, T φ = ∫ y, φ y * f y := fun φ => by
    rw [hT, Distribution.ofFun_apply hloc]
    simp only [smul_eq_mul]
  rw [← hTapp, pairing_bumpMeas']
  exact integral_congr_ae (Eventually.of_forall fun x => hTapp _)

/-- the mass of `bumpMeas n μ R` is `μ(ℂ)` -/
theorem integral_bumpMeas : ∫ y, bumpMeas n μ R y = μ.real univ := by
  have h := integral_bumpMeas_mul' n μ R (fun _ => 1) continuous_const
  simp only [mul_one] at h
  rw [h]
  simp_rw [CircleAvg.integral_bumpTest']
  rw [integral_const, smul_eq_mul, mul_one]

variable {μ R}

/-- if `μ` lives on `B̄(0, R)`, the retraction is invisible:
`T(bumpMeas n μ R) = ∫ T(ψ_{n,x}) dμ(x)` -/
theorem pairing_bumpMeas (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) (T : DistC) :
    T (bumpMeas n μ R) = ∫ x, T (bumpTest n x) ∂μ := by
  rw [pairing_bumpMeas']
  refine integral_congr_ae ?_
  have hae : ∀ᵐ x ∂μ, x ∈ closedBall (0 : ℂ) R := by
    rw [ae_iff]
    exact measure_mono_null (fun x hx => hx) hR
  filter_upwards [hae] with x hx
  rw [mem_closedBall, dist_zero_right] at hx
  rw [ballRetract_of_norm_le hx]

theorem integral_bumpMeas_mul (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) (f : ℂ → ℝ) (hf : Continuous f) :
    ∫ y, bumpMeas n μ R y * f y = ∫ x, (∫ y, bumpTest n x y * f y) ∂μ := by
  have hloc : LocallyIntegrableOn f ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) volume := by
    rw [TopologicalSpace.Opens.coe_top, locallyIntegrableOn_univ]
    exact hf.locallyIntegrable
  set T : DistC := Distribution.ofFun ⊤ f volume ⊤ with hT
  have hTapp : ∀ φ : TestC, T φ = ∫ y, φ y * f y := fun φ => by
    rw [hT, Distribution.ofFun_apply hloc]
    simp only [smul_eq_mul]
  rw [← hTapp, pairing_bumpMeas n hR]
  exact integral_congr_ae (Eventually.of_forall fun x => hTapp _)

/-- **The density identity** `bumpMeas n μ R dx = moll n μ = μ * ψ_n`. -/
theorem withDensity_bumpMeas (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) :
    volume.withDensity (fun y => ENNReal.ofReal (bumpMeas n μ R y)) = moll n μ := by
  have : IsFiniteMeasure (volume.withDensity (fun y => ENNReal.ofReal (bumpMeas n μ R y))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_bumpMeas n μ R).hasFiniteIntegral
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_withDensity_eq_integral_toReal_smul
    (bumpMeas n μ R).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have e : ∀ y, (ENNReal.ofReal (bumpMeas n μ R y)).toReal • f y = bumpMeas n μ R y * f y :=
    fun y => by rw [ENNReal.toReal_ofReal (bumpMeas_nonneg n μ R y), smul_eq_mul]
  simp_rw [e]
  rw [integral_bumpMeas_mul n hR f f.continuous, integral_moll_eq f.continuous.measurable
    (integrable_of_continuous_of_compl_closedBall f.continuous (moll_compl_closedBall hR))]

/-- integrals against `bumpMeas n μ R` are integrals against `moll n μ` -/
theorem integral_mul_bumpMeas (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) (F : ℂ → ℝ) :
    ∫ y, bumpMeas n μ R y * F y = ∫ y, F y ∂moll n μ := by
  rw [← withDensity_bumpMeas n hR, integral_withDensity_eq_integral_toReal_smul
    (bumpMeas n μ R).continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (bumpMeas_nonneg n μ R y), smul_eq_mul]

end bumpMeas

/-! ## The logarithmic potential of `bumpMeas` and the variance of the increments -/

section variance

variable {μ : Measure ℂ} [IsFiniteMeasure μ] {R C α : ℝ}

/-- the Hölder exponent `s = min (α/2) 1` -/
def sExp (α : ℝ) : ℝ := min (α / 2) 1

theorem sExp_pos {α : ℝ} (hα : 0 < α) : 0 < sExp α := lt_min (by positivity) one_pos

theorem sExp_le_one (α : ℝ) : sExp α ≤ 1 := min_le_right _ _

theorem sExp_lt {α : ℝ} (hα : 0 < α) : sExp α < α :=
  (min_le_left _ _).trans_lt (by linarith)

/-- the Hölder constant `2 negMoment / s` of `U_μ` -/
def holdM (μ : Measure ℂ) (C α : ℝ) : ℝ := 2 * negMoment μ C α (sExp α) / sExp α

omit [IsFiniteMeasure μ] in
theorem holdM_nonneg (hb : BallBound μ C α) (hα : 0 < α) : 0 ≤ holdM μ C α :=
  div_nonneg (mul_nonneg zero_le_two (negMoment_nonneg hb (sExp_pos hα) (sExp_lt hα)))
    (sExp_pos hα).le

/-- the potential of `bumpMeas n μ R` is within `holdM · 2^{-ns}` of `U_μ` -/
theorem abs_logPot_bumpMeas_sub_le (hb : BallBound μ C α) (hα : 0 < α)
    (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) (n : ℕ) (x : ℂ) :
    |CircleAvg.logPot (bumpMeas n μ R) x - logPotM μ x| ≤
      ((2 : ℝ)⁻¹ ^ n) ^ sExp α * holdM μ C α := by
  have e : CircleAvg.logPot (bumpMeas n μ R) x = ∫ y, -Real.log ‖x - y‖ ∂moll n μ := by
    rw [← integral_mul_bumpMeas n hR]
    unfold CircleAvg.logPot
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [e, holdM, ← mul_div_assoc]
  exact abs_integral_neg_log_moll_sub_le hb hα hR (sExp_pos hα) (sExp_le_one α) (sExp_lt hα) n x

theorem rpow_sExp_pow (α : ℝ) (n : ℕ) :
    ((2 : ℝ)⁻¹ ^ n) ^ sExp α = ((2 : ℝ)⁻¹ ^ sExp α) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

variable (μ R)

/-- consecutive differences as mean-zero test functions -/
def bumpMeasDiff (n : ℕ) : TestC0 :=
  ⟨bumpMeas (n + 1) μ R - bumpMeas n μ R, by
    show ∫ y, (bumpMeas (n + 1) μ R y - bumpMeas n μ R y) = 0
    rw [integral_sub (integrable_bumpMeas _ μ R) (integrable_bumpMeas _ μ R), integral_bumpMeas,
      integral_bumpMeas, sub_self]⟩

theorem integral_abs_sub_bumpMeas_le (n m : ℕ) :
    ∫ y, |bumpMeas n μ R y - bumpMeas m μ R y| ≤ 2 * μ.real univ := by
  calc ∫ y, |bumpMeas n μ R y - bumpMeas m μ R y|
      ≤ ∫ y, (bumpMeas n μ R y + bumpMeas m μ R y) := by
        refine integral_mono ((integrable_bumpMeas n μ R).sub (integrable_bumpMeas m μ R)).abs
          ((integrable_bumpMeas n μ R).add (integrable_bumpMeas m μ R)) fun y => ?_
        have := bumpMeas_nonneg n μ R y
        have := bumpMeas_nonneg m μ R y
        rw [abs_le]; constructor <;> linarith
    _ = 2 * μ.real univ := by
        rw [integral_add (integrable_bumpMeas n μ R) (integrable_bumpMeas m μ R), integral_bumpMeas,
          integral_bumpMeas]; ring

variable {μ R}

theorem logCov_bumpMeasDiff_le (hb : BallBound μ C α) (hα : 0 < α)
    (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) (n : ℕ) :
    logCov (bumpMeasDiff μ R n).1 (bumpMeasDiff μ R n).1 ≤
      4 * μ.real univ * holdM μ C α * ((2 : ℝ)⁻¹ ^ sExp α) ^ n := by
  have hcoe : ((bumpMeasDiff μ R n).1 : ℂ → ℝ) =
      fun y => bumpMeas (n + 1) μ R y - bumpMeas n μ R y := rfl
  rw [hcoe]
  have hH := holdM_nonneg hb hα
  refine (logCov_sub_le (integrable_bumpMeas _ μ R) (integrable_bumpMeas _ μ R)
    (CircleAvg.integrable_log_mul_test _) (CircleAvg.integrable_log_mul_test _)
    (abs_logPot_bumpMeas_sub_le hb hα hR (n + 1)) (abs_logPot_bumpMeas_sub_le hb hα hR n)).trans ?_
  have hI := integral_abs_sub_bumpMeas_le μ R (n + 1) n
  rw [rpow_sExp_pow, rpow_sExp_pow, pow_succ]
  have hq0 : 0 ≤ (2 : ℝ)⁻¹ ^ sExp α := by positivity
  have hq1 : (2 : ℝ)⁻¹ ^ sExp α ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (sExp_pos hα).le
  have hqn : 0 ≤ ((2 : ℝ)⁻¹ ^ sExp α) ^ n := pow_nonneg hq0 n
  have hm : 0 ≤ μ.real univ := measureReal_nonneg
  have h1 : ((2 : ℝ)⁻¹ ^ sExp α) ^ n * (2 : ℝ)⁻¹ ^ sExp α ≤ ((2 : ℝ)⁻¹ ^ sExp α) ^ n :=
    mul_le_of_le_one_right hqn hq1
  have hE : 0 ≤ ((2 : ℝ)⁻¹ ^ sExp α) ^ n * (2 : ℝ)⁻¹ ^ sExp α * holdM μ C α +
      ((2 : ℝ)⁻¹ ^ sExp α) ^ n * holdM μ C α := by positivity
  calc (((2 : ℝ)⁻¹ ^ sExp α) ^ n * (2 : ℝ)⁻¹ ^ sExp α * holdM μ C α +
        ((2 : ℝ)⁻¹ ^ sExp α) ^ n * holdM μ C α) * ∫ y, |bumpMeas (n + 1) μ R y - bumpMeas n μ R y|
      ≤ (((2 : ℝ)⁻¹ ^ sExp α) ^ n * (2 : ℝ)⁻¹ ^ sExp α * holdM μ C α +
        ((2 : ℝ)⁻¹ ^ sExp α) ^ n * holdM μ C α) * (2 * μ.real univ) :=
          mul_le_mul_of_nonneg_left hI hE
    _ ≤ 4 * μ.real univ * holdM μ C α * ((2 : ℝ)⁻¹ ^ sExp α) ^ n := by
        have h2 : ((2 : ℝ)⁻¹ ^ sExp α) ^ n * (2 : ℝ)⁻¹ ^ sExp α * holdM μ C α ≤
            ((2 : ℝ)⁻¹ ^ sExp α) ^ n * holdM μ C α := mul_le_mul_of_nonneg_right h1 hH
        nlinarith [mul_nonneg hm hH, mul_nonneg (mul_nonneg hm hH) hqn]

end variance

/-! ## Almost sure convergence for every whole-plane GFF -/

/-- `x ↦ ⟨g, ψ_{n,x}⟩` is integrable against a finite measure living on a ball -/
theorem integrable_apply_bumpTest (g : DistC) (n : ℕ) {μ : Measure ℂ} [IsFiniteMeasure μ] {R : ℝ}
    (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) : Integrable (fun x => g (bumpTest n x)) μ :=
  integrable_of_continuous_of_compl_closedBall ((map_continuous g).comp (continuous_bumpTest n)) hR

/-- **`lem:pairing-limits` (a) for every whole-plane GFF and every regular measure**: almost surely
the mollified pairings `∫ ⟨g, ψ_{n,x}⟩ dμ(x)` converge, to `measPairing g μ`. -/
theorem ae_tendsto_measPairing_of_isWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {μ : Measure ℂ} (hμ : IsRegular μ) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ∫ x, g ω (bumpTest n x) ∂μ) atTop
      (𝓝 (GaussianLQG.measPairing (g ω) μ)) := by
  have := hg.gaussian.isProbabilityMeasure
  obtain ⟨hfin, ⟨R, hR⟩, C, α, hα, hb⟩ := hμ
  have hsub : ∀ n ω, g ω (bumpMeas (n + 1) μ R) - g ω (bumpMeas n μ R) =
      g ω (bumpMeasDiff μ R n).1 := fun n ω => by
    rw [← map_sub]; rfl
  have hq0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ sExp α := by positivity
  have hq1 : (2 : ℝ)⁻¹ ^ sExp α < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) (sExp_pos hα)
  have hconv := CircleAvg.ae_tendsto_of_sq_incr_le (P := P) (X := fun n ω => g ω (bumpMeas n μ R))
    (C := 4 * μ.real univ * holdM μ C α) (fun n => ?_) hq0 hq1 (fun n => ?_)
  · filter_upwards [hconv] with ω ⟨a, ha⟩
    have e : ∀ n, g ω (bumpMeas n μ R) = ∫ x, g ω (bumpTest n x) ∂μ := fun n =>
      pairing_bumpMeas n hR (g ω)
    simp_rw [e] at ha
    rw [GaussianLQG.measPairing, ha.limUnder_eq]
    exact ha
  · simp only [hsub]
    exact (CircleAvg.integral_sq_pair hg (bumpMeasDiff μ R n)).1
  · simp only [hsub]
    rw [(CircleAvg.integral_sq_pair hg (bumpMeasDiff μ R n)).2]
    exact logCov_bumpMeasDiff_le hb hα hR n

/-- **Shift by a constant, deterministically**: if the mollified pairings of `g` with `μ` converge,
then `(g + c, μ) = (g, μ) + c μ(ℂ)` for every `c`. -/
theorem measPairing_addConst_of_tendsto {g : DistC} {μ : Measure ℂ} [IsFiniteMeasure μ] {R : ℝ}
    (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) {a : ℝ}
    (ha : Tendsto (fun n => ∫ x, g (bumpTest n x) ∂μ) atTop (𝓝 a)) (c : ℝ) :
    GaussianLQG.measPairing (addConst g c) μ = GaussianLQG.measPairing g μ + c * μ.real univ := by
  have e : ∀ n : ℕ, ∫ x, addConst g c (bumpTest n x) ∂μ =
      (∫ x, g (bumpTest n x) ∂μ) + c * μ.real univ := by
    intro n
    simp_rw [GFFInv.addConst_apply, CircleAvg.integral_bumpTest', one_mul]
    rw [integral_add (integrable_apply_bumpTest g n hR) (integrable_const c), integral_const,
      smul_eq_mul, mul_comm]
  have h2 : Tendsto (fun n : ℕ => ∫ x, addConst g c (bumpTest n x) ∂μ) atTop
      (𝓝 (a + c * μ.real univ)) := by
    simp_rw [e]
    exact ha.add_const _
  rw [GaussianLQG.measPairing, GaussianLQG.measPairing, h2.limUnder_eq, ha.limUnder_eq]

/-- **`(h + c, μ) = (h, μ) + c μ(ℂ)` almost surely, for all `c` at once**, for every whole-plane
GFF and every regular measure. -/
theorem ae_measPairing_addConst_of_isWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {μ : Measure ℂ}
    (hμ : IsRegular μ) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, GaussianLQG.measPairing (addConst (g ω) c) μ =
      GaussianLQG.measPairing (g ω) μ + c * μ.real univ := by
  obtain ⟨hfin, ⟨R, hR⟩, -⟩ := id hμ
  filter_upwards [ae_tendsto_measPairing_of_isWholePlaneGFF hg hμ] with ω hω c
  exact measPairing_addConst_of_tendsto hR hω c

end MeasPair

end SmallGammaGeodesics
