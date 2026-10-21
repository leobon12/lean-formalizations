import SmallGammaGeodesics.Upper.Interfaces
import GaussianLQG.Field.Realization.Pairing
import LQGMetric.Field.CircleAvgPairing
import LQGMetric.Field.CircleAvgIntegral
import LQGMetric.Field.CircleAvgAffine
import LQGMetric.Field.CircleAvgLimit
import LQGMetric.Field.CircleAvgVar
import LQGMetric.Field.MeasurableAvg
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Lemma 4.2′, Step 6 (part 1): mollified pairings with path measures (`lem:pairing-limits`)

For a continuous path `γ : ℝ → ℂ`, `pathMeas γ = γ_*(Leb|[0,1])`; the segment measure is
`λ = segMeasure 0 1 = pathMeas (t ↦ t)` (`segMeasure_eq_pathMeas`). The mollified pairing
`x ↦ ⟨g, ψ_{n,x}⟩` integrated against `pathMeas γ` is the pairing of `g` with the single test
function `bumpPath n γ = ∫₀¹ ψ_{n,γ(t)} dt` (`integral_pathMeas_eq_bumpPath`, from LQGMetric's
`TestIntegral.exists_testIntegral`, as for the circle averages). As a measure,
`bumpPath n γ dx = (pathMeas γ) * ψ_n = moll n (pathMeas γ)` (`withDensity_bumpPath`), so all
integrals against `bumpPath` are integrals against GaussianLQG's mollified measures, with no
integrability side conditions (`integral_mul_bumpPath`).

If `γ` is bi-Lipschitz from below on `[0,1]` (`κ|t − t'| ≤ |γ t − γ t'|`), `pathMeas γ` has the
ball-mass bound `ν(B_r(u)) ≤ (2/κ) r` (`ballBound_pathMeas`). Then the logarithmic potential
`U_ν(x) = ∫ −log|x − w| dν(w)` is `1/2`-Hölder (`abs_logPotM_sub_le`, from GaussianLQG's
`integral_abs_log_sub_le`), the potential of `bumpPath n γ` is within `C 2^{-n/2}` of `U_ν`
(`abs_logPot_bumpPath_sub_le`), and hence `logCov D D ≤ C' 2^{-n/2}` for
`D = bumpPath (n+1) γ − bumpPath n γ`. For every whole-plane GFF `g` this gives a.s. convergence
of the mollified pairings to `measPairing g (pathMeas γ)` (`ae_tendsto_bumpPath`; LQGMetric's
`ae_tendsto_of_sq_incr_le` and `integral_sq_pair`). This is blueprint `lem:pairing-limits` (a),
transferred to every whole-plane GFF without any realization argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped ENNReal NNReal Distributions BoundedContinuousFunction

namespace SmallGammaGeodesics

namespace Coupling42

open LQGMetric GaussianLQG.Realization

/-! ## Path measures -/

/-- the image `γ_*(Leb|[0,1])` of the uniform measure on `[0,1]` -/
def pathMeas (γ : ℝ → ℂ) : Measure ℂ := (volume.restrict (Icc (0 : ℝ) 1)).map γ

instance (γ : ℝ → ℂ) : IsFiniteMeasure (pathMeas γ) :=
  Measure.isFiniteMeasure_map _ _

theorem pathMeas_univ {γ : ℝ → ℂ} (hγ : Measurable γ) : pathMeas γ univ = 1 := by
  rw [pathMeas, Measure.map_apply hγ MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one]

theorem isProbabilityMeasure_pathMeas {γ : ℝ → ℂ} (hγ : Measurable γ) :
    IsProbabilityMeasure (pathMeas γ) := ⟨pathMeas_univ hγ⟩

theorem pathMeas_real_univ {γ : ℝ → ℂ} (hγ : Measurable γ) : (pathMeas γ).real univ = 1 := by
  rw [measureReal_def, pathMeas_univ hγ, ENNReal.toReal_one]

theorem segMeasure_eq_pathMeas :
    GaussianLQG.segMeasure 0 1 = pathMeas (fun t : ℝ => (t : ℂ)) := by
  unfold GaussianLQG.segMeasure pathMeas
  congr 1
  funext u
  simp

theorem pathMeas_compl_eq_zero {γ : ℝ → ℂ} (hγ : Measurable γ) {S : Set ℂ} (hS : MeasurableSet S)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ S) : pathMeas γ Sᶜ = 0 := by
  rw [pathMeas, Measure.map_apply hγ hS.compl, Measure.restrict_apply (hγ hS.compl)]
  convert measure_empty (μ := (volume : Measure ℝ))
  ext t
  simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
  intro hn ht
  exact hn (h t ht)

theorem ae_pathMeas_mem {γ : ℝ → ℂ} (hγ : Measurable γ) {S : Set ℂ} (hS : MeasurableSet S)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ S) : ∀ᵐ w ∂pathMeas γ, w ∈ S := by
  rw [ae_iff]
  have : {a | ¬a ∈ S} = Sᶜ := rfl
  rw [this]
  exact pathMeas_compl_eq_zero hγ hS h

/-- **Ball-mass bound** for a path that is bi-Lipschitz from below on `[0,1]`. -/
theorem ballBound_pathMeas {γ : ℝ → ℂ} (hγ : Measurable γ) {κ : ℝ} (hκ : 0 < κ)
    (hlip : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, κ * |t - t'| ≤ ‖γ t - γ t'‖) :
    BallBound (pathMeas γ) (2 / κ) 1 := by
  intro u r hr _
  rw [Real.rpow_one, pathMeas, Measure.map_apply hγ measurableSet_ball,
    Measure.restrict_apply (hγ measurableSet_ball)]
  set S : Set ℝ := γ ⁻¹' ball u r ∩ Icc 0 1 with hS
  have hdiam : Metric.ediam S ≤ ENNReal.ofReal (2 / κ * r) := by
    refine Metric.ediam_le fun t ht t' ht' => ?_
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hlip t ht.2 t' ht'.2
    have h2 : ‖γ t - γ t'‖ < 2 * r := by
      have ha : dist (γ t) u < r := ht.1
      have hb : dist (γ t') u < r := ht'.1
      rw [← dist_eq_norm]
      calc dist (γ t) (γ t') ≤ dist (γ t) u + dist u (γ t') := dist_triangle _ _ _
        _ < r + r := by rw [dist_comm u]; linarith
        _ = 2 * r := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
    nlinarith
  have hvol := (Real.volume_le_diam S).trans hdiam
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hvol

/-! ## The test function `bumpPath n γ = ∫₀¹ ψ_{n,γ(t)} dt` -/

/-- a bound for `‖γ‖` on `[0,1]` -/
def pathR (γ : C(ℝ, ℂ)) : ℝ :=
  Classical.choose ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    γ.continuous.continuousOn)

theorem norm_le_pathR (γ : C(ℝ, ℂ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖γ t‖ ≤ pathR γ :=
  Classical.choose_spec ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    γ.continuous.continuousOn) t ht

/-- the clamped path `t ↦ γ(proj_{[0,1]} t)` -/
def clampPath (γ : C(ℝ, ℂ)) (t : ℝ) : ℂ := γ (projIcc 0 1 zero_le_one t)

theorem continuous_clampPath (γ : C(ℝ, ℂ)) : Continuous (clampPath γ) :=
  γ.continuous.comp (continuous_subtype_val.comp continuous_projIcc)

theorem norm_clampPath_le (γ : C(ℝ, ℂ)) (t : ℝ) : ‖clampPath γ t‖ ≤ pathR γ :=
  norm_le_pathR γ (projIcc 0 1 zero_le_one t).2

theorem clampPath_of_mem (γ : C(ℝ, ℂ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    clampPath γ t = γ t := by
  rw [clampPath, projIcc_of_mem _ ht]

/-- the compact `closedBall 0 (R_γ + 1)` containing all the supports -/
def pathK (γ : C(ℝ, ℂ)) : TopologicalSpace.Compacts ℂ :=
  ⟨closedBall 0 (pathR γ + 1), isCompact_closedBall _ _⟩

theorem support_bumpTest_clamp (n : ℕ) (γ : C(ℝ, ℂ)) (t : ℝ) :
    Function.support (bumpTest n (clampPath γ t)) ⊆ (pathK γ : Set ℂ) := by
  intro y hy
  by_contra hK
  apply hy
  apply CircleAvg.bumpTest_eq_zero
  have h1 : pathR γ + 1 < dist y 0 := by
    simpa [pathK] using hK
  have h2 := norm_clampPath_le γ t
  have h3 := dist_triangle y (clampPath γ t) 0
  have h4 : dist (clampPath γ t) 0 = ‖clampPath γ t‖ := dist_zero_right _
  linarith

/-- the curve `t ↦ ψ_{n, γ(proj t)}` in `𝓓_K` -/
def pathCurve (n : ℕ) (γ : C(ℝ, ℂ)) (t : ℝ) : 𝓓^{⊤}_{pathK γ}(ℂ, ℝ) :=
  ContDiffMapSupportedIn.of_support_subset (bumpTest n (clampPath γ t)).contDiff
    (support_bumpTest_clamp n γ t)

theorem continuous_pathCurve (n : ℕ) (γ : C(ℝ, ℂ)) : Continuous (pathCurve n γ) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  set G := iteratedFDeriv ℝ i (bumpTest n 0 : ℂ → ℝ)
  have hGc : Continuous G := (bumpTest n 0).contDiff.continuous_iteratedFDeriv
    (by exact_mod_cast le_top)
  have hGu : UniformContinuous G :=
    ((bumpTest n 0).hasCompactSupport.iteratedFDeriv i).uniformContinuous_of_continuous hGc
  have hval : ∀ t y, (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i (pathCurve n γ t)) y =
      G (y - clampPath γ t) := by
    intro t y
    rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
    exact CircleAvg.iteratedFDeriv_bumpTest n _ i y
  rw [Metric.continuous_iff]
  intro t₀ ε hε
  obtain ⟨δ, hδ, hG⟩ := Metric.uniformContinuous_iff.mp hGu (ε / 2) (by positivity)
  obtain ⟨η, hη, hc⟩ := Metric.continuous_iff.mp (continuous_clampPath γ) t₀ δ hδ
  refine ⟨η, hη, fun t ht => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (by positivity)).mpr fun y => ?_)
    (half_lt_self hε)
  simp only [Function.comp_apply, hval]
  refine (hG ?_).le
  rw [dist_eq_norm, sub_sub_sub_cancel_left, ← dist_eq_norm']
  exact hc t ht

theorem exists_bumpPath (n : ℕ) (γ : C(ℝ, ℂ)) :
    ∃ I : 𝓓^{⊤}_{pathK γ}(ℂ, ℝ), (∀ y, I y = ∫ t in (0 : ℝ)..1, pathCurve n γ t y) ∧
      ∀ T : 𝓓^{⊤}_{pathK γ}(ℂ, ℝ) →L[ℝ] ℝ, T I = ∫ t in (0 : ℝ)..1, T (pathCurve n γ t) :=
  TestIntegral.exists_testIntegral 0 1 (continuous_pathCurve n γ)

/-- `∫₀¹ ψ_{n,γ(t)} dt` as a test function -/
def bumpPath (n : ℕ) (γ : C(ℝ, ℂ)) : TestC :=
  TestFunction.ofSupportedIn (subset_univ _) (exists_bumpPath n γ).choose

theorem pathCurve_eq (n : ℕ) (γ : C(ℝ, ℂ)) (t : ℝ) :
    TestFunction.ofSupportedIn (subset_univ _) (pathCurve n γ t) = bumpTest n (clampPath γ t) := by
  ext y; rfl

theorem bumpPath_apply (n : ℕ) (γ : C(ℝ, ℂ)) (y : ℂ) :
    bumpPath n γ y = ∫ t in (0 : ℝ)..1, bumpTest n (γ t) y := by
  show (exists_bumpPath n γ).choose y = _
  rw [(exists_bumpPath n γ).choose_spec.1 y]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  show bumpTest n (clampPath γ t) y = bumpTest n (γ t) y
  rw [clampPath_of_mem γ ht]

/-- **Distributions commute with the path integral**: `T(bumpPath n γ) = ∫₀¹ T(ψ_{n,γ(t)}) dt`. -/
theorem pairing_bumpPath (T : DistC) (n : ℕ) (γ : C(ℝ, ℂ)) :
    T (bumpPath n γ) = ∫ t in (0 : ℝ)..1, T (bumpTest n (γ t)) := by
  have h := (exists_bumpPath n γ).choose_spec.2
    (T.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _)))
  show T (TestFunction.ofSupportedIn (subset_univ _) (exists_bumpPath n γ).choose) = _
  have e1 : T (TestFunction.ofSupportedIn (subset_univ _) (exists_bumpPath n γ).choose) =
      (T.comp (TestFunction.ofSupportedInCLM ℝ (subset_univ _))) (exists_bumpPath n γ).choose :=
    rfl
  rw [e1, h]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  show T (TestFunction.ofSupportedIn (subset_univ _) (pathCurve n γ t)) = T (bumpTest n (γ t))
  rw [pathCurve_eq, clampPath_of_mem γ ht]

theorem bumpPath_nonneg (n : ℕ) (γ : C(ℝ, ℂ)) (y : ℂ) : 0 ≤ bumpPath n γ y := by
  rw [bumpPath_apply]
  exact intervalIntegral.integral_nonneg zero_le_one fun t _ => CircleAvg.bumpTest_nonneg n _ y

/-- the mollified pairing with `pathMeas γ` is the pairing with `bumpPath n γ` -/
theorem integral_pathMeas_eq_bumpPath (T : DistC) (n : ℕ) (γ : C(ℝ, ℂ)) :
    ∫ x, T (bumpTest n x) ∂pathMeas γ = T (bumpPath n γ) := by
  have hc : Continuous fun x => T (bumpTest n x) := (map_continuous T).comp (continuous_bumpTest n)
  rw [pairing_bumpPath, pathMeas, integral_map γ.continuous.measurable.aemeasurable
    hc.aestronglyMeasurable, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc]

/-- `measPairing g (pathMeas γ)` is the limit of the pairings with `bumpPath n γ` -/
theorem measPairing_pathMeas (g : DistC) (γ : C(ℝ, ℂ)) :
    GaussianLQG.measPairing g (pathMeas γ) = limUnder atTop fun n => g (bumpPath n γ) := by
  unfold GaussianLQG.measPairing
  simp_rw [integral_pathMeas_eq_bumpPath]

/-! ## `bumpPath n γ` is the density of `moll n (pathMeas γ)` -/

theorem continuous_bumpPath (n : ℕ) (γ : C(ℝ, ℂ)) : Continuous (bumpPath n γ) :=
  (bumpPath n γ).continuous

theorem integrable_bumpPath (n : ℕ) (γ : C(ℝ, ℂ)) : Integrable (bumpPath n γ) :=
  (bumpPath n γ).continuous.integrable_of_hasCompactSupport (bumpPath n γ).hasCompactSupport

theorem integral_bumpTest_mul_eq (n : ℕ) (γ : C(ℝ, ℂ)) (f : ℂ →ᵇ ℝ) :
    ∫ y, bumpPath n γ y * f y = ∫ x, (∫ y, bumpTest n x y * f y) ∂pathMeas γ := by
  have hloc : LocallyIntegrableOn (f : ℂ → ℝ) ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)
      volume := by
    rw [TopologicalSpace.Opens.coe_top, locallyIntegrableOn_univ]
    exact f.continuous.locallyIntegrable
  set T : DistC := Distribution.ofFun ⊤ (f : ℂ → ℝ) volume ⊤ with hT
  have hTapp : ∀ φ : TestC, T φ = ∫ y, φ y * f y := fun φ => by
    rw [hT, Distribution.ofFun_apply hloc]
    simp only [smul_eq_mul]
  rw [← hTapp, pairing_bumpPath, pathMeas, integral_map γ.continuous.measurable.aemeasurable
    (measurable_integral_bump_mul n f.continuous).aestronglyMeasurable,
    intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [hTapp]

/-- **The density identity** `bumpPath n γ dx = moll n (pathMeas γ)`. -/
theorem withDensity_bumpPath (n : ℕ) (γ : C(ℝ, ℂ)) :
    volume.withDensity (fun y => ENNReal.ofReal (bumpPath n γ y)) = moll n (pathMeas γ) := by
  have : IsFiniteMeasure (volume.withDensity (fun y => ENNReal.ofReal (bumpPath n γ y))) :=
    isFiniteMeasure_withDensity_ofReal (integrable_bumpPath n γ).hasFiniteIntegral
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_bumpPath n γ).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have e : ∀ y, (ENNReal.ofReal (bumpPath n γ y)).toReal • f y = bumpPath n γ y * f y :=
    fun y => by rw [ENNReal.toReal_ofReal (bumpPath_nonneg n γ y), smul_eq_mul]
  simp_rw [e]
  rw [integral_bumpTest_mul_eq, integral_moll_eq f.continuous.measurable
    (integrable_of_continuous_of_compl_closedBall f.continuous
      (moll_compl_closedBall (ρ := pathMeas γ) (R := pathR γ) ?_))]
  exact pathMeas_compl_eq_zero γ.continuous.measurable measurableSet_closedBall fun t ht => by
    rw [mem_closedBall, dist_zero_right]; exact norm_le_pathR γ ht

/-- integrals against `bumpPath n γ` are integrals against `moll n (pathMeas γ)` -/
theorem integral_mul_bumpPath (n : ℕ) (γ : C(ℝ, ℂ)) (F : ℂ → ℝ) :
    ∫ y, bumpPath n γ y * F y = ∫ y, F y ∂moll n (pathMeas γ) := by
  rw [← withDensity_bumpPath, integral_withDensity_eq_integral_toReal_smul
    (continuous_bumpPath n γ).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (bumpPath_nonneg n γ y), smul_eq_mul]

theorem integral_bumpPath (n : ℕ) (γ : C(ℝ, ℂ)) : ∫ y, bumpPath n γ y = 1 := by
  have h := integral_mul_bumpPath n γ (fun _ => 1)
  simp only [mul_one, integral_const, smul_eq_mul] at h
  rw [h, measureReal_def, moll_univ, pathMeas_univ γ.continuous.measurable, ENNReal.toReal_one]

/-! ## Logarithmic potentials -/

/-- the logarithmic potential `U_ν(x) = ∫ −log|x − w| dν(w)` of a measure -/
def logPotM (ν : Measure ℂ) (x : ℂ) : ℝ := ∫ w, -Real.log ‖x - w‖ ∂ν

section potential

variable {ν : Measure ℂ} [IsFiniteMeasure ν] {C α R : ℝ}

/-- `U_ν` is `s`-Hölder (GaussianLQG `integral_abs_log_sub_le`) -/
theorem abs_logPotM_sub_le (hb : BallBound ν C α) (hα : 0 < α)
    (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hsα : s < α)
    (x x' : ℂ) :
    |logPotM ν x - logPotM ν x'| ≤ ‖x - x'‖ ^ s * (2 * negMoment ν C α s) / s := by
  obtain ⟨-, hbd⟩ := integral_abs_log_sub_le hb hα hs hs1 hsα x x'
  have h1 : Integrable (fun w => -Real.log ‖x - w‖) ν := (integrable_log_norm_sub hb hα hR x).neg
  have h2 : Integrable (fun w => -Real.log ‖x' - w‖) ν :=
    (integrable_log_norm_sub hb hα hR x').neg
  rw [logPotM, logPotM, ← integral_sub h1 h2]
  refine (abs_integral_le_integral_abs).trans (le_trans (le_of_eq ?_) hbd)
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [neg_sub_neg, abs_sub_comm]

theorem measurable_neg_log_norm_sub (x : ℂ) : Measurable fun y : ℂ => -Real.log ‖x - y‖ :=
  (measurable_log_norm_sub x).neg

theorem integrable_neg_log_moll (hb : BallBound ν C α) (hα : 0 < α)
    (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) (n : ℕ) (x : ℂ) :
    Integrable (fun y => -Real.log ‖x - y‖) (moll n ν) :=
  (integrable_log_norm_sub (ballBound_moll hb) hα (moll_compl_closedBall hR) x).neg

theorem integrable_prod_neg_log (hb : BallBound ν C α) (hα : 0 < α)
    (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) (n : ℕ) (x : ℂ) :
    Integrable (fun p : ℂ × ℂ => -Real.log ‖x - (p.1 + p.2)‖) (ν.prod (bumpLaw n)) :=
  (integrable_map_measure (measurable_neg_log_norm_sub x).aestronglyMeasurable
    measurable_add_pair.aemeasurable).mp (integrable_neg_log_moll hb hα hR n x)

/-- `∫ −log|x − y| d(ν * ψ_n)(y) = ∫ U_ν(x − z) dψ_n(z)` -/
theorem integral_neg_log_moll (hb : BallBound ν C α) (hα : 0 < α)
    (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) (n : ℕ) (x : ℂ) :
    ∫ y, -Real.log ‖x - y‖ ∂(moll n ν) = ∫ z, logPotM ν (x - z) ∂(bumpLaw n) := by
  rw [moll, integral_map measurable_add_pair.aemeasurable
    (measurable_neg_log_norm_sub x).aestronglyMeasurable,
    integral_prod_symm _ (integrable_prod_neg_log hb hα hR n x)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [logPotM]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  congr 3
  ring

/-- **The potential of the mollified measure is within `C 2^{-ns}` of `U_ν`.** -/
theorem abs_integral_neg_log_moll_sub_le (hb : BallBound ν C α) (hα : 0 < α)
    (hR : ν (closedBall (0 : ℂ) R)ᶜ = 0) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hsα : s < α)
    (n : ℕ) (x : ℂ) :
    |∫ y, -Real.log ‖x - y‖ ∂(moll n ν) - logPotM ν x| ≤
      ((2 : ℝ)⁻¹ ^ n) ^ s * (2 * negMoment ν C α s) / s := by
  rw [integral_neg_log_moll hb hα hR n x]
  have hint : Integrable (fun z => logPotM ν (x - z)) (bumpLaw n) := by
    refine (integrable_prod_neg_log hb hα hR n x).integral_prod_right.congr
      (Eventually.of_forall fun z => ?_)
    simp only [logPotM]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    congr 3
    ring
  have e : ∫ z, logPotM ν (x - z) ∂bumpLaw n - logPotM ν x =
      ∫ z, (logPotM ν (x - z) - logPotM ν x) ∂bumpLaw n := by
    rw [integral_sub hint (integrable_const _), integral_const, probReal_univ, one_smul]
  rw [e, ← Real.norm_eq_abs]
  have hK : 0 ≤ 2 * negMoment ν C α s / s :=
    div_nonneg (mul_nonneg zero_le_two (negMoment_nonneg hb hs hsα)) hs.le
  refine (norm_integral_le_of_norm_le_const (C := ((2 : ℝ)⁻¹ ^ n) ^ s *
    (2 * negMoment ν C α s) / s) ?_).trans (by rw [probReal_univ, mul_one])
  filter_upwards [ae_bumpLaw_norm_le n] with z hz
  rw [Real.norm_eq_abs]
  refine (abs_logPotM_sub_le hb hα hR hs hs1 hsα (x - z) x).trans ?_
  rw [show x - z - x = -z by ring, norm_neg]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg z) hz hs.le)
    (mul_nonneg zero_le_two (negMoment_nonneg hb hs hsα))) hs.le

end potential

/-! ## `logCov` of differences of probability densities -/

/-- if the log potentials of two densities are uniformly close to one function `V`, the
log-covariance of their difference is small -/
theorem logCov_sub_le {f₁ f₂ : ℂ → ℝ} (h1 : Integrable f₁) (h2 : Integrable f₂)
    (h1' : ∀ x, Integrable (fun y => -Real.log ‖x - y‖ * f₁ y))
    (h2' : ∀ x, Integrable (fun y => -Real.log ‖x - y‖ * f₂ y)) {V : ℂ → ℝ} {e₁ e₂ : ℝ}
    (he₁ : ∀ x, |CircleAvg.logPot f₁ x - V x| ≤ e₁)
    (he₂ : ∀ x, |CircleAvg.logPot f₂ x - V x| ≤ e₂) :
    logCov (fun y => f₁ y - f₂ y) (fun y => f₁ y - f₂ y) ≤
      (e₁ + e₂) * ∫ y, |f₁ y - f₂ y| := by
  rw [CircleAvg.logCov_eq_integral_logPot]
  have hpot : ∀ x, CircleAvg.logPot (fun y => f₁ y - f₂ y) x =
      CircleAvg.logPot f₁ x - CircleAvg.logPot f₂ x := by
    intro x
    unfold CircleAvg.logPot
    rw [← integral_sub (h1' x) (h2' x)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  have hbd : ∀ x, |CircleAvg.logPot (fun y => f₁ y - f₂ y) x| ≤ e₁ + e₂ := by
    intro x
    rw [hpot]
    have := abs_sub_le (CircleAvg.logPot f₁ x) (V x) (CircleAvg.logPot f₂ x)
    have h3 := he₂ x
    rw [abs_sub_comm] at h3
    linarith [he₁ x]
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((h1.sub h2).abs.const_mul (e₁ + e₂))
    (Eventually.of_forall fun x => ?_)).trans (le_of_eq (integral_const_mul _ _))
  rw [Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hbd x) (abs_nonneg _)

/-! ## Mollified pairings with a path measure converge almost surely -/

section pathGFF

variable (γ : C(ℝ, ℂ)) {κ : ℝ}

/-- the half-exponent of the Hölder bounds for path measures -/
def sH : ℝ := 1 / 2

/-- the Hölder constant `2 negMoment / s` for the potential of `pathMeas γ` (`α = 1`, `s = 1/2`) -/
def holdPath (κ : ℝ) : ℝ := 2 * negMoment (pathMeas γ) (2 / κ) 1 sH / sH

theorem pathMeas_compl_closedBall : pathMeas γ (closedBall (0 : ℂ) (pathR γ))ᶜ = 0 :=
  pathMeas_compl_eq_zero γ.continuous.measurable measurableSet_closedBall fun t ht => by
    rw [mem_closedBall, dist_zero_right]; exact norm_le_pathR γ ht

theorem integrable_neg_log_mul_bumpPath (hb : BallBound (pathMeas γ) (2 / κ) 1) (n : ℕ)
    (x : ℂ) : Integrable (fun y => -Real.log ‖x - y‖ * bumpPath n γ y) := by
  have hi := integrable_neg_log_moll hb one_pos (pathMeas_compl_closedBall γ) n x
  rw [← withDensity_bumpPath, integrable_withDensity_iff_integrable_smul'
    (continuous_bumpPath n γ).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hi
  refine hi.congr (Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (bumpPath_nonneg n γ y), smul_eq_mul]
  ring

/-- the potential of `bumpPath n γ` is within `holdPath · 2^{-n/2}` of `U_{pathMeas γ}` -/
theorem abs_logPot_bumpPath_sub_le (hb : BallBound (pathMeas γ) (2 / κ) 1)
    (n : ℕ) (x : ℂ) :
    |CircleAvg.logPot (bumpPath n γ) x - logPotM (pathMeas γ) x| ≤
      ((2 : ℝ)⁻¹ ^ n) ^ sH * holdPath γ κ := by
  have e : CircleAvg.logPot (bumpPath n γ) x = ∫ y, -Real.log ‖x - y‖ ∂moll n (pathMeas γ) := by
    rw [← integral_mul_bumpPath]
    unfold CircleAvg.logPot
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [e, holdPath, ← mul_div_assoc]
  exact abs_integral_neg_log_moll_sub_le hb one_pos (pathMeas_compl_closedBall γ)
    (by norm_num [sH]) (by norm_num [sH]) (by norm_num [sH]) n x

theorem rpow_sH_pow (n : ℕ) : ((2 : ℝ)⁻¹ ^ n) ^ sH = ((2 : ℝ)⁻¹ ^ sH) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- consecutive differences as mean-zero test functions -/
def bumpPathDiff (n : ℕ) : TestC0 :=
  ⟨bumpPath (n + 1) γ - bumpPath n γ, by
    show ∫ y, (bumpPath (n + 1) γ y - bumpPath n γ y) = 0
    rw [integral_sub (integrable_bumpPath _ γ) (integrable_bumpPath _ γ), integral_bumpPath,
      integral_bumpPath, sub_self]⟩

theorem integral_abs_sub_bumpPath_le (n m : ℕ) :
    ∫ y, |bumpPath n γ y - bumpPath m γ y| ≤ 2 := by
  calc ∫ y, |bumpPath n γ y - bumpPath m γ y|
      ≤ ∫ y, (bumpPath n γ y + bumpPath m γ y) := by
        refine integral_mono ((integrable_bumpPath n γ).sub (integrable_bumpPath m γ)).abs
          ((integrable_bumpPath n γ).add (integrable_bumpPath m γ)) fun y => ?_
        have := bumpPath_nonneg n γ y
        have := bumpPath_nonneg m γ y
        rw [abs_le]; constructor <;> linarith
    _ = 2 := by
        rw [integral_add (integrable_bumpPath n γ) (integrable_bumpPath m γ), integral_bumpPath,
          integral_bumpPath]; norm_num

theorem logCov_bumpPathDiff_le (hb : BallBound (pathMeas γ) (2 / κ) 1) (n : ℕ) :
    logCov (bumpPathDiff γ n).1 (bumpPathDiff γ n).1 ≤
      4 * holdPath γ κ * ((2 : ℝ)⁻¹ ^ sH) ^ n := by
  have hcoe : ((bumpPathDiff γ n).1 : ℂ → ℝ) = fun y => bumpPath (n + 1) γ y - bumpPath n γ y :=
    rfl
  rw [hcoe]
  have hH : 0 ≤ holdPath γ κ := by
    unfold holdPath
    exact div_nonneg (mul_nonneg zero_le_two (negMoment_nonneg hb (by norm_num [sH])
      (by norm_num [sH]))) (by norm_num [sH])
  refine (logCov_sub_le (integrable_bumpPath _ γ) (integrable_bumpPath _ γ)
    (integrable_neg_log_mul_bumpPath γ hb (n + 1)) (integrable_neg_log_mul_bumpPath γ hb n)
    (abs_logPot_bumpPath_sub_le γ hb (n + 1)) (abs_logPot_bumpPath_sub_le γ hb n)).trans ?_
  have hI := integral_abs_sub_bumpPath_le γ (n + 1) n
  rw [rpow_sH_pow, rpow_sH_pow, pow_succ]
  have hq0 : 0 ≤ (2 : ℝ)⁻¹ ^ sH := by positivity
  have hq1 : (2 : ℝ)⁻¹ ^ sH ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num [sH])
  have hqn : 0 ≤ ((2 : ℝ)⁻¹ ^ sH) ^ n := pow_nonneg hq0 n
  have h1 : ((2 : ℝ)⁻¹ ^ sH) ^ n * (2 : ℝ)⁻¹ ^ sH ≤ ((2 : ℝ)⁻¹ ^ sH) ^ n :=
    mul_le_of_le_one_right hqn hq1
  have hE : 0 ≤ ((2 : ℝ)⁻¹ ^ sH) ^ n * (2 : ℝ)⁻¹ ^ sH * holdPath γ κ +
      ((2 : ℝ)⁻¹ ^ sH) ^ n * holdPath γ κ := by positivity
  calc (((2 : ℝ)⁻¹ ^ sH) ^ n * (2 : ℝ)⁻¹ ^ sH * holdPath γ κ +
        ((2 : ℝ)⁻¹ ^ sH) ^ n * holdPath γ κ) * ∫ y, |bumpPath (n + 1) γ y - bumpPath n γ y|
      ≤ (((2 : ℝ)⁻¹ ^ sH) ^ n * (2 : ℝ)⁻¹ ^ sH * holdPath γ κ +
        ((2 : ℝ)⁻¹ ^ sH) ^ n * holdPath γ κ) * 2 := mul_le_mul_of_nonneg_left hI hE
    _ ≤ 4 * holdPath γ κ * ((2 : ℝ)⁻¹ ^ sH) ^ n := by nlinarith

/-- **`lem:pairing-limits` (a) for every whole-plane GFF**: almost surely the mollified pairings
with `pathMeas γ` converge, to `measPairing g (pathMeas γ)`. -/
theorem ae_tendsto_bumpPath {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → DistC}
    (hg : IsWholePlaneGFF g P) (hκ : 0 < κ)
    (hlip : ∀ t ∈ Icc (0 : ℝ) 1, ∀ t' ∈ Icc (0 : ℝ) 1, κ * |t - t'| ≤ ‖γ t - γ t'‖) :
    ∀ᵐ ω ∂P, Tendsto (fun n => g ω (bumpPath n γ)) atTop
      (𝓝 (GaussianLQG.measPairing (g ω) (pathMeas γ))) := by
  have := hg.gaussian.isProbabilityMeasure
  have hb := ballBound_pathMeas γ.continuous.measurable hκ hlip
  have hsub : ∀ n ω, g ω (bumpPath (n + 1) γ) - g ω (bumpPath n γ) =
      g ω (bumpPathDiff γ n).1 := fun n ω => by
    rw [← map_sub]; rfl
  have hq0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ sH := by positivity
  have hq1 : (2 : ℝ)⁻¹ ^ sH < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num [sH])
  have hconv := CircleAvg.ae_tendsto_of_sq_incr_le (P := P) (X := fun n ω => g ω (bumpPath n γ))
    (C := 4 * holdPath γ κ) (fun n => ?_) hq0 hq1 (fun n => ?_)
  · filter_upwards [hconv] with ω ⟨a, ha⟩
    rw [measPairing_pathMeas, ha.limUnder_eq]
    exact ha
  · simp only [hsub]
    exact (CircleAvg.integral_sq_pair hg (bumpPathDiff γ n)).1
  · simp only [hsub]
    rw [(CircleAvg.integral_sq_pair hg (bumpPathDiff γ n)).2]
    exact logCov_bumpPathDiff_le γ hb n

end pathGFF

end Coupling42

end SmallGammaGeodesics
