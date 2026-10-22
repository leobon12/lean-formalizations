import HigherDimLQGMetric.Sphere.Var

/-!
# The cross covariance of sphere averages with test functions, in potential form

Packet F3 (Phase A, block A1), target 2 (second formula, iterated form). Blueprint Lemma `lem:tilt`
(`Cov(X, ⟨H, φ⟩) = ∫ k φ` with `k` the log potential of `ν = σ_{r,z} - σ_{ρ,w}`, packet F4).

For `d ≥ 2`, positive radii and `f` bounded with bounded support (`IsBddSupp f M D`):

`logCov(σ_{r,z}, σ_{ρ,w}, f⁺ dz, f⁻ dz) = ∫ f(y) (F_{r,z}(y) - F_{ρ,w}(y)) dy`

with `F_{r,z} = logPotM σ_{r,z}` (continuous, `logPotM_sphMeas`) — `logCov_sphMeas_posM_eq_integral`
(Fubini; the four product integrals are finite by HigherDimLFPP's `logPairable_of_growthBound`,
since `f^± dz` has a linear growth bound, F2's `posM_real_closedBall_le`). Hence for an LGF and
mean-zero `φ` (`IsWholeSpaceLGF.covariance_sphereAvg_sub_apply_eq_integral`):

`Cov(h_r(z) - h_ρ(w), ⟨h, φ⟩) = ∫ φ(y) (F_{r,z}(y) - F_{ρ,w}(y)) dy
  = ∫∫ log|u - y|⁻¹ (σ_{r,z} - σ_{ρ,w})(du) φ(y) dy`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- `f⁺ dz` has a linear growth bound at scale `1` (`d ≥ 1`). -/
theorem growthBound_posM [NeZero d] {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D) :
    HigherDimLFPP.GrowthBound (posM f) (M * volBall d + (posM f).real univ) 1 := by
  have := isFiniteMeasure_posM hf
  intro x s hs
  rw [div_one]
  have h1 := posM_real_closedBall_le hf x hs
  have h2 : (posM f).real (closedBall x s) ≤ (posM f).real univ := measureReal_mono (subset_univ _)
  have h3 : 0 ≤ M * volBall d := mul_nonneg hf.nonneg volBall_nonneg
  rcases le_total 1 s with hs1 | hs1
  · rw [min_eq_left hs1, mul_one]; linarith
  · rw [min_eq_right hs1]; exact h1

/-- `I(μ, f⁺ dz) = ∫ f⁺(y) F_μ(y) dy` for a sphere measure `μ = σ_{r,z}`. -/
theorem logEnergy_sphMeas_posM (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) (z : Rd d) {f : Rd d → ℝ}
    {M D : ℝ} (hf : IsBddSupp f M D) :
    logEnergy (sphMeas r z) (posM f) = ∫ y, max (f y) 0 * logPotM (sphMeas r z) y := by
  have : NeZero d := ⟨by omega⟩
  have := isFiniteMeasure_posM hf
  have := isFiniteMeasure_posM hf.neg
  have := isProbabilityMeasure_sphMeas (show 1 ≤ d by omega) r z
  -- integrability on the product
  have hB : (0 : ℝ) ≤ 2 ^ d := by positivity
  set B := max (2 ^ d) (M * volBall d + (posM f).real univ + (M * volBall d +
    (posM (-f)).real univ)) with hBdef
  have g1 : HigherDimLFPP.GrowthBound (sphMeas r z) B (min r 1) := by
    rw [← sphLaw_zero]
    exact growthBound_mono_const (growthBound_mono_scale (growthBound_sphLaw hd hr z 0) hB
      (lt_min hr one_pos) (min_le_left _ _)) (le_max_left _ _) (lt_min hr one_pos)
  have hm1 : M * volBall d + (posM f).real univ ≤ B := by
    have := mul_nonneg hf.nonneg (volBall_nonneg (d := d))
    have : 0 ≤ (posM (-f)).real univ := measureReal_nonneg
    exact le_max_of_le_right (by linarith)
  have hm2 : M * volBall d + (posM (-f)).real univ ≤ B := by
    have := mul_nonneg hf.nonneg (volBall_nonneg (d := d))
    have : 0 ≤ (posM f).real univ := measureReal_nonneg
    exact le_max_of_le_right (by linarith)
  have g3 : HigherDimLFPP.GrowthBound (posM f) B (min r 1) :=
    growthBound_mono_scale (growthBound_mono_const (growthBound_posM hf) hm1 one_pos)
      (le_max_of_le_left hB) (lt_min hr one_pos) (min_le_right _ _)
  have g4 : HigherDimLFPP.GrowthBound (posM (-f)) B (min r 1) := by
    have := growthBound_posM hf.neg
    exact growthBound_mono_scale (growthBound_mono_const this hm2 one_pos)
      (le_max_of_le_left hB) (lt_min hr one_pos) (min_le_right _ _)
  set D' := ‖z‖ + |r| + |D| with hD'
  have s1 : ∀ᵐ x ∂(sphMeas r z), ‖x‖ ≤ D' := by
    rw [← sphLaw_zero]
    filter_upwards [ae_sphLaw_norm_le r z 0] with x hx
    have := abs_nonneg D
    simp only [abs_zero, add_zero] at hx
    linarith
  have s3 : ∀ᵐ x ∂(posM f), ‖x‖ ≤ D' := by
    filter_upwards [ae_posM_norm_le hf] with x hx
    have := le_abs_self D
    have : 0 ≤ ‖z‖ + |r| := by positivity
    linarith
  have s4 : ∀ᵐ x ∂(posM (-f)), ‖x‖ ≤ D' := by
    filter_upwards [ae_posM_norm_le hf.neg] with x hx
    have := le_abs_self D
    have : 0 ≤ ‖z‖ + |r| := by positivity
    linarith
  have hP := HigherDimLFPP.logPairable_of_growthBound (lt_min hr one_pos) (lt_min hr one_pos)
    g1 g1 g3 g4 s1 s1 s3 s4
  have hint : Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖)
      ((sphMeas r z).prod (posM f)) :=
    (hP.integrable_prod (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
      (HigherDimLFPP.FieldAux.le_add_four₃ _ _ _ _)).neg
  -- Fubini in the order `dμ` inside
  unfold logEnergy
  rw [integral_prod_symm _ hint]
  have hU : ∀ y : Rd d, ∫ x, -Real.log ‖(x, y).1 - (x, y).2‖ ∂(sphMeas r z) =
      logPotM (sphMeas r z) y := by
    intro y
    unfold logPotM
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [norm_sub_rev]
  simp_rw [hU]
  rw [posM, integral_withDensity_eq_integral_toReal_smul hf.measurable.ennreal_ofReal
    (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [ENNReal.toReal_ofReal', smul_eq_mul]

theorem integrable_mul_continuous_of_isBddSupp {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D)
    {g : Rd d → ℝ} (hg : Continuous g) : Integrable fun y => f y * g y := by
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : Rd d) D).exists_bound_of_continuousOn
    hg.continuousOn
  refine Integrable.mono' (g := fun y => M * K * (closedBall (0 : Rd d) D).indicator 1 y)
    ((integrable_indicator_closedBall D).const_mul (M * K))
    (hf.measurable.mul hg.measurable).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  by_cases hy : y ∈ closedBall (0 : Rd d) D
  · rw [indicator_of_mem hy, Pi.one_apply, mul_one, norm_mul]
    exact mul_le_mul (hf.norm_le y) (hK y hy) (norm_nonneg _)
      (hf.nonneg)
  · rw [hf.eq_zero_of_notMem hy, zero_mul, norm_zero]
    rw [indicator_of_notMem hy, mul_zero]

/-- **Potential form of the cross term**: `logCov(σ_{r,z}, σ_{ρ,w}, f⁺ dz, f⁻ dz) =
∫ f(y) (F_{r,z}(y) - F_{ρ,w}(y)) dy` (`d ≥ 2`, `r, ρ > 0`, `f` bounded with bounded support). -/
theorem logCov_sphMeas_posM_eq_integral (hd : 2 ≤ d) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (z w : Rd d) {f : Rd d → ℝ} {M D : ℝ} (hf : IsBddSupp f M D) :
    HigherDimLFPP.logCov (sphMeas r z) (sphMeas ρ w) (posM f) (posM (-f)) =
      ∫ y, f y * (logPotM (sphMeas r z) y - logPotM (sphMeas ρ w) y) := by
  have c1 := continuous_logPotM_sphMeas hd hr z
  have c2 := continuous_logPotM_sphMeas hd hρ w
  have i1 := integrable_mul_continuous_of_isBddSupp hf.posPart c1
  have i2 := integrable_mul_continuous_of_isBddSupp hf.neg.posPart c1
  have i3 := integrable_mul_continuous_of_isBddSupp hf.posPart c2
  have i4 := integrable_mul_continuous_of_isBddSupp hf.neg.posPart c2
  rw [logCov_eq_logEnergy, logEnergy_sphMeas_posM hd hr z hf, logEnergy_sphMeas_posM hd hr z hf.neg,
    logEnergy_sphMeas_posM hd hρ w hf, logEnergy_sphMeas_posM hd hρ w hf.neg,
    ← integral_sub_sub_add i1 i2 i3 i4]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  have hf' : max (f y) 0 - max (-f y) 0 = f y := max_zero_sub_max_neg_zero_eq_self _
  simp only [Pi.neg_apply]
  rw [show f y * (logPotM (sphMeas r z) y - logPotM (sphMeas ρ w) y) =
    (max (f y) 0 - max (-f y) 0) * (logPotM (sphMeas r z) y - logPotM (sphMeas ρ w) y) by
      rw [hf']]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- **Cross covariance in potential form** (`d ≥ 2`, `r, ρ > 0`, mean-zero `φ`):
`Cov(h_r(z) - h_ρ(w), ⟨h, φ⟩) = ∫ φ(y) (F_{r,z}(y) - F_{ρ,w}(y)) dy`, with
`F_{r,z}(y) = ∫ log|u - y|⁻¹ dσ_{r,z}(u)`. -/
theorem IsWholeSpaceLGF.covariance_sphereAvg_sub_apply_eq_integral (hd : 2 ≤ d)
    (hh : IsWholeSpaceLGF h P) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (z w : Rd d)
    (φ : TestRd0 d) :
    cov[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w, fun ω => h ω φ.1; P] =
      ∫ y, φ.1 y * (logPotM (sphMeas r z) y - logPotM (sphMeas ρ w) y) := by
  obtain ⟨M, D, hMD⟩ := exists_isBddSupp_testOn φ.1
  rw [hh.covariance_sphereAvg_sub_apply hd hr hρ z w φ]
  exact logCov_sphMeas_posM_eq_integral hd hr hρ z w hMD

end HigherDimLQGMetric
