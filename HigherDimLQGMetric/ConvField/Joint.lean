import HigherDimLQGMetric.ConvField.RadialEnvelope

/-! Joint continuity of the full radial convolution integral. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

set_option maxHeartbeats 1000000 in
theorem l2b_continuous_radial_integral (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (T : DistRd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    Continuous fun p : ℝ × Rd d =>
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
        convKernelEps κ (Real.exp p.1) (r • e₁ d) * sphereAvg T r p.2 := by
  let F : (ℝ × Rd d) → ℝ → ℝ := fun p r =>
    r ^ (d - 1) * convKernelEps κ (Real.exp p.1) (r • e₁ d) * sphereAvg T r p.2
  change Continuous fun p : ℝ × Rd d => ∫ r in Ioi (0 : ℝ), F p r
  rw [continuous_iff_continuousAt]
  intro p₀
  obtain ⟨N, hN⟩ := exists_nat_gt (‖p₀.2‖ + 2)
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  let a : ℝ := Real.exp (p₀.1 - 1)
  let b : ℝ := Real.exp (p₀.1 + 1)
  have ha : 0 < a := Real.exp_pos _
  obtain ⟨M, hM0, hM⟩ := l2b_exists_uniform_kernel_decay hd hκ (a := a) (b := b) ha
  let bound : ℝ → ℝ := fun r => M * C *
    (r ^ (d - 1) * l2b_decayEnvelope d r * l2b_growthWeight r)
  have hbound : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (l2b_integrable_radial_growth_decayEnvelope d hd).const_mul (M * C)
  have hnu : closedBall p₀.1 1 ∈ 𝓝 p₀.1 := closedBall_mem_nhds _ (by norm_num)
  have hnz : closedBall (0 : Rd d) (N : ℝ) ∈ 𝓝 p₀.2 := by
    apply Filter.mem_of_superset (isOpen_ball.mem_nhds ?_) ball_subset_closedBall
    rw [mem_ball, dist_zero_right]
    linarith
  have hnb : {p : ℝ × Rd d | p.1 ∈ closedBall p₀.1 1 ∧
      p.2 ∈ closedBall (0 : Rd d) (N : ℝ)} ∈ 𝓝 p₀ :=
    mem_nhds_prod_iff.mpr ⟨closedBall p₀.1 1, hnu,
      closedBall 0 (N : ℝ), hnz, by rintro p ⟨hu, hz⟩; exact ⟨hu, hz⟩⟩
  apply continuousAt_of_dominated (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F) (bound := bound)
  · filter_upwards with p
    have hrad : ContinuousOn (fun r : ℝ => sphereAvg T r p.2) (Ioi 0) := by
      change ContinuousOn ((fun q : ℝ × Rd d => sphereAvg T q.1 q.2) ∘
        (fun r : ℝ => (r, p.2))) (Ioi 0)
      exact hcont.comp (by fun_prop : ContinuousOn (fun r : ℝ => (r, p.2)) (Ioi 0))
        (by simp [MapsTo])
    have hK : Continuous fun r : ℝ =>
        convKernelEps κ (Real.exp p.1) (r • e₁ d) := by
      change Continuous ((fun q : ℝ × ℝ =>
        convKernelEps κ (Real.exp q.1) (q.2 • e₁ d)) ∘ (fun r : ℝ => (p.1, r)))
      exact (l2b_continuous_kernelAxis_exp hd hκ).comp (by fun_prop)
    have hF : ContinuousOn (F p) (Ioi 0) :=
      ((continuous_id.pow _).mul hK).continuousOn.mul hrad
    exact hF.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [hnb] with p hp
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hu : p.1 ∈ closedBall p₀.1 1 := hp.1
    have hz : p.2 ∈ closedBall (0 : Rd d) (N : ℝ) := hp.2
    have hule : p₀.1 - 1 ≤ p.1 ∧ p.1 ≤ p₀.1 + 1 := by
      rw [mem_closedBall, Real.dist_eq, abs_le] at hu
      constructor <;> linarith [hu.1, hu.2]
    have hεa : a ≤ Real.exp p.1 := Real.exp_le_exp.mpr hule.1
    have hεb : Real.exp p.1 ≤ b := Real.exp_le_exp.mpr hule.2
    have hk := hM (Real.exp p.1) hεa hεb (r • e₁ d)
    have hknorm : ‖r • e₁ d‖ = r := by
      rw [norm_smul, HigherDimLFPP.norm_e₁ (by omega : 0 < d), mul_one,
        Real.norm_eq_abs, abs_of_pos hr]
    rw [hknorm] at hk
    have hg := hC p.2 hz r hr
    have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr.le _
    have hW0 : 0 ≤ l2b_growthWeight r :=
      (zero_le_one.trans (le_max_right _ _)).trans (le_max_right _ _)
    have henv0 : 0 ≤ l2b_decayEnvelope d r := by dsimp [l2b_decayEnvelope]; positivity
    have he : l2b_decayEnvelope d r =
        (1 + r) ^ (-((d : ℝ) + 1)) := by
      have hr0 : 0 < r := hr
      simp [l2b_decayEnvelope, max_eq_left hr0.le]
    rw [← he] at hk
    change |F p r| ≤ bound r
    dsimp [F, bound]
    rw [abs_mul, abs_mul, abs_of_nonneg hp0]
    calc r ^ (d - 1) * |convKernelEps κ (Real.exp p.1) (r • e₁ d)| *
          |sphereAvg T r p.2|
        ≤ r ^ (d - 1) * (M * l2b_decayEnvelope d r) *
            (C * l2b_growthWeight r) := by
          gcongr
      _ = M * C * (r ^ (d - 1) * l2b_decayEnvelope d r *
          l2b_growthWeight r) := by ring
  · exact hbound
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hs : ContinuousAt (fun p : ℝ × Rd d => sphereAvg T r p.2) p₀ := by
      have hmem : (r, p₀.2) ∈ Ioi 0 ×ˢ univ := ⟨hr, trivial⟩
      have hc : ContinuousAt (fun q : ℝ × Rd d => sphereAvg T q.1 q.2) (r, p₀.2) :=
        hcont.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
      exact hc.comp₂ continuousAt_const continuousAt_snd
    have hK : ContinuousAt (fun p : ℝ × Rd d =>
        convKernelEps κ (Real.exp p.1) (r • e₁ d)) p₀ := by
      have hc : ContinuousAt (fun q : ℝ × ℝ =>
          convKernelEps κ (Real.exp q.1) (q.2 • e₁ d)) (p₀.1, r) :=
        (l2b_continuous_kernelAxis_exp hd hκ).continuousAt
      exact hc.comp₂ continuousAt_fst continuousAt_const
    exact ((continuousAt_const.mul hK).mul hs)

end HigherDimLQGMetric
