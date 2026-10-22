import HigherDimLQGMetric.Trunc.Param
import HigherDimLQGMetric.ConvField.RadialCont

/-! Joint continuity of the localized radial convolution integral. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ} {κ : Rd d → ℝ}

set_option maxHeartbeats 1000000 in
theorem l2c_continuous_trunc_radial_integral (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (T : DistRd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2)
      (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    Continuous fun p : ℝ × Rd d =>
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * l2c_axisFactor κ p.1 r *
        sphereAvg T r p.2 := by
  let F : (ℝ × Rd d) → ℝ → ℝ := fun p r =>
    r ^ (d - 1) * l2c_axisFactor κ p.1 r * sphereAvg T r p.2
  change Continuous fun p : ℝ × Rd d => ∫ r in Ioi (0 : ℝ), F p r
  rw [continuous_iff_continuousAt]
  intro p₀
  let R : ℝ := Real.exp (p₀.1 + 1) + 1
  have hR1 : 1 ≤ R := by dsimp [R]; linarith [Real.exp_pos (p₀.1 + 1)]
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (‖p₀.2‖ + 2)
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  let U : Set ℝ := closedBall p₀.1 1
  have hUc : IsCompact U := isCompact_closedBall _ _
  have hKc : IsCompact (U ×ˢ Icc (0 : ℝ) R) := hUc.prod isCompact_Icc
  have hfactor : Continuous fun q : ℝ × ℝ => |l2c_axisFactor κ q.1 q.2| :=
    (l2c_continuous_axisFactor hd hκ).abs
  obtain ⟨M₀, hM₀⟩ := hKc.bddAbove_image hfactor.continuousOn
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ u ∈ U, ∀ r ∈ Icc (0 : ℝ) R,
      |l2c_axisFactor κ u r| ≤ M := by
    intro u hu r hr
    exact (hM₀ (mem_image_of_mem _ (show (u, r) ∈ U ×ˢ Icc 0 R from ⟨hu, hr⟩))).trans
      (le_max_left _ _)
  let B : ℝ := R ^ (d - 1) * max (Real.log R) 1 + 1
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  let D : ℝ := M * C * B
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  let bound : ℝ → ℝ := (Icc (0 : ℝ) R).indicator fun _ => D
  have hboundI : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  have hnu : U ∈ 𝓝 p₀.1 := closedBall_mem_nhds _ (by norm_num)
  have hnz : closedBall (0 : Rd d) (N : ℝ) ∈ 𝓝 p₀.2 := by
    apply Filter.mem_of_superset (isOpen_ball.mem_nhds ?_) ball_subset_closedBall
    rw [mem_ball, dist_zero_right]
    linarith
  have hnb : {p : ℝ × Rd d | p.1 ∈ U ∧ p.2 ∈ closedBall (0 : Rd d) (N : ℝ)} ∈ 𝓝 p₀ :=
    mem_nhds_prod_iff.mpr ⟨U, hnu, closedBall 0 (N : ℝ), hnz, by
      rintro p ⟨hu, hz⟩
      exact ⟨hu, hz⟩⟩
  apply continuousAt_of_dominated (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F) (bound := bound)
  · filter_upwards with p
    have hrad : ContinuousOn (fun r : ℝ => sphereAvg T r p.2) (Ioi 0) := by
      have hmap : ContinuousOn (fun r : ℝ => (r, p.2)) (Ioi 0) := by fun_prop
      change ContinuousOn ((fun q : ℝ × Rd d => sphereAvg T q.1 q.2) ∘
        (fun r : ℝ => (r, p.2))) (Ioi 0)
      exact hcont.comp hmap (by simp [MapsTo])
    have hF : ContinuousOn (F p) (Ioi 0) := by
      dsimp [F]
      exact ((continuous_id.pow _).mul
        ((l2c_continuous_axisFactor hd hκ).comp
          (continuous_const.prodMk continuous_id))).continuousOn.mul hrad
    exact hF.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [hnb] with p hp
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hu : p.1 ∈ U := hp.1
    have hz : p.2 ∈ closedBall (0 : Rd d) (N : ℝ) := hp.2
    have hr0 : 0 < r := hr
    by_cases hrR : r ≤ R
    · have hrK : r ∈ Icc (0 : ℝ) R := ⟨hr0.le, hrR⟩
      have hprod := l2b_polar_log_weight_bounded hd hR1 hr0 hrR
      have hgrow := hC p.2 hz r hr0
      have hW0 : 0 ≤ l2b_growthWeight r := by
        dsimp [l2b_growthWeight]
        exact le_max_of_le_right (zero_le_one.trans (le_max_right _ _))
      have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr0.le _
      have hax := hM p.1 hu r hrK
      have hmain : |F p r| ≤ D := by
        dsimp [F, D, B]
        rw [abs_mul, abs_mul, abs_of_nonneg hp0]
        calc r ^ (d - 1) * |l2c_axisFactor κ p.1 r| * |sphereAvg T r p.2|
            ≤ r ^ (d - 1) * M * (C * l2b_growthWeight r) := by
              gcongr
            _ = M * C * (r ^ (d - 1) * l2b_growthWeight r) := by ring
            _ ≤ M * C * B := by
              apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM0 hC0)
              exact hprod
      simpa only [Real.norm_eq_abs, bound, Set.indicator_of_mem hrK] using hmain
    · have hzero : l2c_axisFactor κ p.1 r = 0 := by
        apply l2c_axisFactor_eq_zero hd
        have hp1 : p.1 ≤ p₀.1 + 1 := by
          have hpu : p.1 ∈ closedBall p₀.1 1 := hu
          rw [mem_closedBall, Real.dist_eq, abs_le] at hpu
          linarith [hpu.2]
        calc Real.exp p.1 ≤ Real.exp (p₀.1 + 1) := Real.exp_le_exp.2 hp1
          _ ≤ R := by dsimp [R]; linarith
          _ ≤ r := le_of_not_ge hrR
      have hnot : r ∉ Icc (0 : ℝ) R := fun hh => hrR hh.2
      simp [F, hzero, bound, Set.indicator_of_notMem hnot]
  · exact hboundI
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hs : ContinuousAt (fun p : ℝ × Rd d => sphereAvg T r p.2) p₀ := by
      have hmem : (r, p₀.2) ∈ Ioi 0 ×ˢ univ := ⟨hr, trivial⟩
      have hc : ContinuousAt (fun q : ℝ × Rd d => sphereAvg T q.1 q.2) (r, p₀.2) :=
        hcont.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
      exact hc.comp₂ continuousAt_const continuousAt_snd
    have hfac : ContinuousAt (fun p : ℝ × Rd d => l2c_axisFactor κ p.1 r) p₀ :=
      (l2c_continuous_axisFactor hd hκ).continuousAt.comp
        (by fun_prop : ContinuousAt (fun p : ℝ × Rd d => (p.1, r)) p₀)
    exact ((continuousAt_const.mul hfac).mul hs)

end HigherDimLQGMetric
