import SupercriticalConformalCovariance.TV.MixtureBridge
import LQGMetric.Papers.MQ.HarmGrad

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric QuantumZipper Filter Topology InnerProductSpace

namespace SupercriticalConformalCovariance.TV

/-- The fixed cutoff of a harmonic increment has Dirichlet energy bounded by
its squared oscillation on a slightly larger disk. -/
theorem exists_energy_bound_fixed_cutoff (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {L : ℝ} (hL : 2 * R + 4 < L)
      {D : TopologicalSpace.Opens ℂ} (hBD : ball (0 : ℂ) L ⊆ D)
      {g : ℂ → ℝ} (hg : InnerProductSpace.HarmonicOnNhd g D)
      {T : DistC} (hT : ∀ φ : TestOn D,
        restrictTo D T φ = ∫ x, g x * φ x)
      {M : ℝ} (hM : 0 ≤ M)
      (hb : ∀ y ∈ closedBall (0 : ℂ) (2 * R + 3), |g y - g 0| ≤ M),
      dirichletEnergyOn D
        (smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) T) ≤ K * M ^ 2 := by
  let χ := innerCutoff R hR
  have hχs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (χ : ℂ → ℝ) := χ.contDiff
  obtain ⟨C, hC⟩ := (hχs.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (χ.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ (χ : ℂ → ℝ) 0)).trans (hC 0)
  let K : ℝ := (2 * Real.pi)⁻¹ * ((C + 8) ^ 2 * ((2 * R + 2) ^ 2 * Real.pi))
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro L hL D hBD g hg T hT M hM hb
  let F : ℂ → ℝ := fun y => χ y * (g y - g 0)
  have hFeq : smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) T = F := by
    funext y
    exact smoothCutoffShift_eq_of_harmonic hR hL hBD hg hT y
  rw [hFeq]
  have hχle (y : ℂ) : |χ y| ≤ 1 := by
    rw [abs_of_nonneg χ.nonneg]
    exact χ.le_one
  have hχ0 (y : ℂ) (hy : 2 * R + 2 ≤ ‖y‖) : χ y = 0 := by
    apply χ.zero_of_le_dist
    simpa [χ, innerCutoff, dist_zero_right] using hy
  have hgd (y : ℂ) (hy : y ∈ closedBall (0 : ℂ) (2 * R + 2)) :
      ‖fderiv ℝ g y‖ ≤ 8 * M := by
    have hy0 : ‖y‖ ≤ 2 * R + 2 := by
      simpa [mem_closedBall, dist_zero_right] using hy
    have hsub : ball y 1 ⊆ D := by
      intro w hw
      apply hBD
      rw [mem_ball, dist_zero_right]
      have hw' : ‖w - y‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
      have htri : ‖w‖ ≤ ‖w - y‖ + ‖y‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w - y) y
      linarith
    have hbound : ∀ w ∈ ball y 1, |g w - g 0| ≤ M := by
      intro w hw
      apply hb w
      rw [mem_closedBall, dist_zero_right]
      have hw' : ‖w - y‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hw
      have htri : ‖w‖ ≤ ‖w - y‖ + ‖y‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w - y) y
      linarith
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hkey := LQGMetric.MQ.norm_fderiv_le_of_harmonic (w := y)
      (s := 1) (M := M + η / 8) (a := g 0) (by norm_num) (by linarith)
      (hg.mono hsub) (fun w hw => (hbound w hw).trans (by linarith))
    norm_num at hkey
    linarith
  have hzero (y : ℂ) (hy : 2 * R + 2 < ‖y‖) : F =ᶠ[𝓝 y] 0 := by
    have ho : IsOpen {w : ℂ | 2 * R + 2 < ‖w‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [ho.mem_nhds hy] with w hw
    simp [F, hχ0 w hw.le]
  have hderiv (y : ℂ) :
      ‖fderiv ℝ F y‖ ^ 2 ≤
        (closedBall (0 : ℂ) (2 * R + 2)).indicator
          (fun _ => ((C + 8) * M) ^ 2) y := by
    by_cases hy : y ∈ closedBall (0 : ℂ) (2 * R + 2)
    · rw [indicator_of_mem hy]
      have hyD : y ∈ D := hBD (by
        rw [mem_ball, dist_zero_right]
        have := mem_closedBall.1 hy
        rw [dist_zero_right] at this
        linarith)
      have hGd : HasFDerivAt g (fderiv ℝ g y) y :=
        ((HarmonicAt.analyticAt (hg y hyD)).differentiableAt).hasFDerivAt
      have hFd : HasFDerivAt F _ y := (hχs.differentiable (by simp) y).hasFDerivAt.mul
        (hGd.sub_const (g 0))
      rw [hFd.fderiv]
      have hnorm : ‖(g y - g 0) • fderiv ℝ (χ : ℂ → ℝ) y +
          χ y • fderiv ℝ g y‖ ≤ (C + 8) * M := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        have hgy : |g y - g 0| ≤ M := hb y (by
          exact (closedBall_subset_closedBall (by linarith) hy))
        have h1 : |g y - g 0| * ‖fderiv ℝ (χ : ℂ → ℝ) y‖ ≤ M * C :=
          mul_le_mul hgy (hC y) (norm_nonneg _) hM
        have h2 : |χ y| * ‖fderiv ℝ g y‖ ≤ 8 * M := by
          calc _ ≤ 1 * (8 * M) :=
              mul_le_mul (hχle y) (hgd y hy) (norm_nonneg _) zero_le_one
            _ = _ := by ring
        linarith
      rw [add_comm]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    · have hy' : 2 * R + 2 < ‖y‖ := by
        rw [mem_closedBall, dist_zero_right, not_le] at hy
        exact hy
      rw [indicator_of_notMem hy, (hzero y hy').fderiv_eq]
      simp
  unfold dirichletEnergyOn
  have hint : Integrable ((closedBall (0 : ℂ) (2 * R + 2)).indicator
      (fun _ : ℂ => ((C + 8) * M) ^ 2)) := by
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    exact integrableOn_const measure_closedBall_lt_top.ne
  have hinner : (∫ y in D, ‖fderiv ℝ F y‖ ^ 2) ≤
      ((C + 8) * M) ^ 2 * ((2 * R + 2) ^ 2 * Real.pi) := by
    calc
    ∫ y in D, ‖fderiv ℝ F y‖ ^ 2
        ≤ ∫ y in D, (closedBall (0 : ℂ) (2 * R + 2)).indicator
            (fun _ => ((C + 8) * M) ^ 2) y :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
            hint.integrableOn (Eventually.of_forall hderiv)
    _ ≤ ∫ y, (closedBall (0 : ℂ) (2 * R + 2)).indicator
            (fun _ => ((C + 8) * M) ^ 2) y :=
          setIntegral_le_integral hint (Eventually.of_forall fun _ =>
            indicator_nonneg (fun _ _ => sq_nonneg _) _)
    _ = ((C + 8) * M) ^ 2 * ((2 * R + 2) ^ 2 * Real.pi) := by
          rw [integral_indicator_const _ measurableSet_closedBall, measureReal_def,
            Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal,
            NNReal.coe_real_pi, smul_eq_mul]
          ring
  calc
    (2 * Real.pi)⁻¹ * (∫ y in D, ‖fderiv ℝ F y‖ ^ 2)
        ≤ (2 * Real.pi)⁻¹ *
            (((C + 8) * M) ^ 2 * ((2 * R + 2) ^ 2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hinner (inv_nonneg.2 (by positivity))
    _ = K * M ^ 2 := by dsimp [K]; ring

end SupercriticalConformalCovariance.TV
