import HigherDimLQGMetric.ConvField.RadialWeightIntegrable

/-! Dominated convergence of the compact radial truncations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem l2b_integrable_radial_sphereAvg (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (T : DistRd d) (z : Rd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) *
      convKernelEps κ ε (r • e₁ d) * sphereAvg T r z) (Ioi (0 : ℝ)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  have hz : z ∈ closedBall (0 : Rd d) (N : ℝ) := by
    rw [mem_closedBall, dist_zero_right]
    exact le_of_lt hN
  have hKc : Continuous fun r : ℝ => convKernelEps κ ε (r • e₁ d) := by
    dsimp [convKernelEps]
    exact continuous_const.mul
      ((convKernel_contDiff (by omega) hκ).continuous.comp
        ((continuous_const : Continuous fun _ : ℝ => ε⁻¹).smul
          (continuous_id.smul continuous_const)))
  have hrad : ContinuousOn (fun r : ℝ => sphereAvg T r z) (Ioi 0) := by
    change ContinuousOn ((fun p : ℝ × Rd d => sphereAvg T p.1 p.2) ∘
      (fun r : ℝ => (r, z))) (Ioi 0)
    exact hcont.comp (by fun_prop : ContinuousOn (fun r : ℝ => (r, z)) (Ioi 0))
      (by simp [MapsTo])
  have hmeas : AEStronglyMeasurable (fun r : ℝ => r ^ (d - 1) *
      convKernelEps κ ε (r • e₁ d) * sphereAvg T r z)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((continuous_id.pow _).mul hKc).continuousOn.mul hrad).aestronglyMeasurable
      measurableSet_Ioi
  have hsource : IntegrableOn (fun r : ℝ => C *
      |r ^ (d - 1) * convKernelEps κ ε (r • e₁ d) * l2b_growthWeight r|)
      (Ioi (0 : ℝ)) :=
    (l2b_integrable_radial_growth_kernel hd hκ hε).norm.const_mul C
  apply hsource.mono' hmeas
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun r hr => ?_)
  have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr.le _
  have hW0 : 0 ≤ l2b_growthWeight r :=
    (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
  have hg := hC z hz r hr
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp0,
    abs_of_nonneg hW0]
  calc r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| * |sphereAvg T r z|
      ≤ r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
          (C * l2b_growthWeight r) := by gcongr
    _ = C * (r ^ (d - 1) * |convKernelEps κ ε (r • e₁ d)| *
        l2b_growthWeight r) := by ring

set_option maxHeartbeats 1000000 in
theorem l2b_tendsto_radial_trunc (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε)
    (T : DistRd d) (z : Rd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    Tendsto (fun n : ℕ => ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
      l2b_axisFactor κ n (Real.log ε) r * sphereAvg T r z) atTop
      (𝓝 (∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        convKernelEps κ ε (r • e₁ d) * sphereAvg T r z)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  have hz : z ∈ closedBall (0 : Rd d) (N : ℝ) := by
    rw [mem_closedBall, dist_zero_right]
    exact le_of_lt hN
  let K : ℝ → ℝ := fun r => convKernelEps κ ε (r • e₁ d)
  let g : ℝ → ℝ := fun r => r ^ (d - 1) * K r * sphereAvg T r z
  let F : ℕ → ℝ → ℝ := fun n r => g r *
    radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d))
  let bound : ℝ → ℝ := fun r => C * |r ^ (d - 1) * K r * l2b_growthWeight r|
  have hbound : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (l2b_integrable_radial_growth_kernel hd hκ hε).norm.const_mul C
  have hKc : Continuous K := by
    dsimp [K, convKernelEps]
    exact continuous_const.mul
      ((convKernel_contDiff (by omega) hκ).continuous.comp
        ((continuous_const : Continuous fun _ : ℝ => ε⁻¹).smul
          (continuous_id.smul continuous_const)))
  have hrad : ContinuousOn (fun r : ℝ => sphereAvg T r z) (Ioi 0) := by
    change ContinuousOn ((fun p : ℝ × Rd d => sphereAvg T p.1 p.2) ∘
      (fun r : ℝ => (r, z))) (Ioi 0)
    exact hcont.comp (by fun_prop : ContinuousOn (fun r : ℝ => (r, z)) (Ioi 0))
      (by simp [MapsTo])
  have hgc : ContinuousOn g (Ioi 0) :=
    ((continuous_id.pow _).mul hKc).continuousOn.mul hrad
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    have hcut : Continuous fun r : ℝ =>
        radialProfile d (((n : ℝ) + 1)⁻¹ • (r • e₁ d)) :=
      (radialProfile d).contDiff.continuous.comp
        ((continuous_const : Continuous fun _ : ℝ => ((n : ℝ) + 1)⁻¹).smul
          (continuous_id.smul continuous_const))
    exact (hgc.mul hcut.continuousOn).aestronglyMeasurable measurableSet_Ioi
  have hdom (n : ℕ) : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖F n r‖ ≤ bound r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr.le _
    have hW0 : 0 ≤ l2b_growthWeight r :=
      (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
    have hcut0 := radialProfile_nonneg (((n : ℝ) + 1)⁻¹ • (r • e₁ d))
    have hcut1 := radialProfile_le_one (((n : ℝ) + 1)⁻¹ • (r • e₁ d))
    have hgr := hC z hz r hr
    dsimp [F, g, bound]
    rw [abs_mul, abs_mul, abs_mul,
      abs_of_nonneg hp0, abs_of_nonneg hcut0]
    have hbase0 : 0 ≤ r ^ (d - 1) * |K r| := mul_nonneg hp0 (abs_nonneg _)
    have hmain : r ^ (d - 1) * |K r| * |sphereAvg T r z| ≤
        C * |r ^ (d - 1) * K r * l2b_growthWeight r| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hW0]
      calc r ^ (d - 1) * |K r| * |sphereAvg T r z|
          ≤ r ^ (d - 1) * |K r| * (C * l2b_growthWeight r) :=
            mul_le_mul_of_nonneg_left hgr hbase0
        _ = C * (r ^ (d - 1) * |K r| * l2b_growthWeight r) := by ring
    exact (mul_le_of_le_one_right (by positivity) hcut1).trans hmain
  have hlim : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun n : ℕ => F n r) atTop (𝓝 (g r)) := by
    filter_upwards with r
    have he : (fun n : ℕ => F n r) =ᶠ[atTop] fun _ => g r := by
      filter_upwards [l2b_cutoff_eventually_one (0 : Rd d) (r • e₁ d)] with n hn
      dsimp [F]
      simpa using congrArg (g r * ·) hn
    exact tendsto_const_nhds.congr' he.symm
  have ht := tendsto_integral_of_dominated_convergence bound hFm hbound hdom hlim
  convert ht using 1
  · funext n
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp [F, g, l2b_axisFactor]
    rw [Real.exp_log hε]
    ring

end HigherDimLQGMetric
