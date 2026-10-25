import SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath.EndSaving
import LQGMetric.Papers.GM.S5.Tubes56Diam




 
set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath


 

theorem outer_endpoint_inward_grid
    (b s : ℝ) (hb : 0 < b) (hs : 0 < s) (hsmall : s < b)
    (v : ℂ) (hv : v ∈ Metric.sphere (0 : ℂ) b) :
    ∃ j : ℤ × ℤ,
      v ∈ Metric.ball (LQGMetric.GM.gridPt (s / 100) j) s ∧
      LQGMetric.GM.gridPt (s / 100) j ∈ Metric.ball (0 : ℂ) b := by
  let t : ℝ := s / (2 * b)
  let y : ℂ := (1 - t) • v
  have ht0 : 0 < t := div_pos hs (by positivity)
  have ht1 : t < 1 := by
    dsimp [t]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * b)).2
    linarith only [hsmall, hb]
  have hvnorm : ‖v‖ = b := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hv
  have htEq : t * b = s / 2 := by
    dsimp [t]
    field_simp
  have hynorm : ‖y‖ = b - s / 2 := by
    change ‖((1 - t : ℝ) : ℂ) * v‖ = b - s / 2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr ht1), hvnorm]
    linarith only [htEq]
  have hvy : dist v y = s / 2 := by
    rw [dist_eq_norm]
    have heq : v - y = t • v := by
      calc
        v - y = (1 : ℝ) • v - (1 - t) • v := by simp only [one_smul, y]
        _ = ((1 : ℝ) - (1 - t)) • v := (sub_smul _ _ _).symm
        _ = t • v := by ring_nf
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hvnorm]
    exact htEq
  have hσ : 0 < s / 100 := by positivity
  obtain ⟨j, hj⟩ := LQGMetric.GM.exists_gridPt_near hσ y
  have hjdist : dist y (LQGMetric.GM.gridPt (s / 100) j) < s / 50 := by
    rw [dist_eq_norm]
    have hval : 2 * (s / 100) = s / 50 := by ring
    simpa only [hval] using hj
  refine ⟨j, ?_, ?_⟩
  · rw [Metric.mem_ball]
    have htri := dist_triangle v y (LQGMetric.GM.gridPt (s / 100) j)
    linarith only [htri, hvy, hjdist, hs]
  · rw [Metric.mem_ball, dist_zero_right]
    have hnorm : ‖LQGMetric.GM.gridPt (s / 100) j‖ ≤
        dist (LQGMetric.GM.gridPt (s / 100) j) y + ‖y‖ := by
      simpa only [dist_eq_norm, sub_add_cancel] using
        norm_add_le (LQGMetric.GM.gridPt (s / 100) j - y) y
    have hj' : dist (LQGMetric.GM.gridPt (s / 100) j) y < s / 50 := by
      simpa only [dist_comm] using hjdist
    linarith only [hnorm, hynorm, hj', hs]

 

theorem endpoint_mesh_centers
    (b : Set.Ioi (0 : ℝ)) (a : Set.Ioo (3 / 4 : ℝ) 1)
    (s : ℝ) (hs : 0 < s)
    (hsmall : 100 * s ≤ (1 - (a : ℝ)) * (b : ℝ))
    (u v : ℂ)
    (hu : u ∈ Metric.sphere (0 : ℂ) ((a : ℝ) * b))
    (hv : v ∈ Metric.sphere (0 : ℂ) b) :
    ∃ i j : ℤ × ℤ,
      let z := LQGMetric.GM.gridPt (s / 100) i
      let w := LQGMetric.GM.gridPt (s / 100) j
      z ∈ Metric.ball (0 : ℂ) b ∧
      w ∈ Metric.ball (0 : ℂ) b ∧
      u ∈ Metric.ball z s ∧ v ∈ Metric.ball w s ∧
      ((1 - (a : ℝ)) / 2) * (b : ℝ) ≤ dist z w ∧
      ((1 - (a : ℝ)) / 2) * (b : ℝ) ≤
        Metric.infDist z (Metric.sphere (0 : ℂ) b) := by
  have hb := b.property
  have ha0 : 0 < (a : ℝ) := lt_trans (by norm_num : (0 : ℝ) < 3 / 4) a.property.1
  have hag : 0 < 1 - (a : ℝ) := sub_pos.mpr a.property.2
  have hGapLt : (1 - (a : ℝ)) * (b : ℝ) < (b : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right (by linarith only [ha0] :
      1 - (a : ℝ) < 1) hb
    simpa only [one_mul] using hmul
  have hsB : s < (b : ℝ) := by linarith only [hsmall, hGapLt, hs]
  have hσ : 0 < s / 100 := by positivity
  have hmesh : 100 * s ≤ (b : ℝ) - (a : ℝ) * b := by
    convert hsmall using 1
    ring
  obtain ⟨i, hi⟩ := LQGMetric.GM.exists_gridPt_near hσ u
  obtain ⟨j, hvj, hwball⟩ := outer_endpoint_inward_grid
    b s hb hs hsB v hv
  let z := LQGMetric.GM.gridPt (s / 100) i
  let w := LQGMetric.GM.gridPt (s / 100) j
  have huz : dist u z < s / 50 := by
    rw [dist_eq_norm]
    have hval : 2 * (s / 100) = s / 50 := by ring
    simpa only [z, hval] using hi
  have hvw : dist v w < s := by
    simpa only [w, Metric.mem_ball] using hvj
  have hu0 : dist u (0 : ℂ) = (a : ℝ) * b := by
    simpa only [Metric.mem_sphere] using hu
  have hv0 : dist v (0 : ℂ) = (b : ℝ) := by
    simpa only [Metric.mem_sphere] using hv
  have hz0 : dist z (0 : ℂ) < (a : ℝ) * b + s / 50 := by
    have htri := dist_triangle z u (0 : ℂ)
    have hzu : dist z u < s / 50 := by simpa only [dist_comm] using huz
    linarith only [htri, hzu, hu0]
  have hzball : z ∈ Metric.ball (0 : ℂ) b := by
    rw [Metric.mem_ball]
    linarith only [hz0, hmesh, hs]
  have hsep0 : (1 - (a : ℝ)) * b ≤ dist u v := by
    have h := (le_abs_self (dist v (0 : ℂ) - dist u (0 : ℂ))).trans
      (abs_dist_sub_le v u 0)
    rw [hv0, hu0, dist_comm] at h
    nlinarith only [h]
  have hsep : ((1 - (a : ℝ)) / 2) * b ≤ dist z w := by
    have htri1 := dist_triangle u z w
    have htri2 := dist_triangle u w v
    have hwv : dist w v < s := by simpa only [dist_comm] using hvw
    nlinarith only [hsep0, htri1, htri2, huz, hwv, hmesh, hs]
  have hclear : ((1 - (a : ℝ)) / 2) * b ≤
      Metric.infDist z (Metric.sphere (0 : ℂ) b) := by
    apply (Metric.le_infDist ⟨v, hv⟩).2
    intro y hy
    have hy0 : dist y (0 : ℂ) = (b : ℝ) := by
      simpa only [Metric.mem_sphere] using hy
    have htri := dist_triangle y z (0 : ℂ)
    have hzy : dist z y = dist y z := dist_comm z y
    nlinarith only [hy0, htri, hz0, hmesh, hzy, hs]
  refine ⟨i, j, hzball, hwball, ?_, ?_, hsep, hclear⟩
  · rw [Metric.mem_ball]
    exact lt_trans huz (by linarith only [hs] : s / 50 < s)
  · exact hvj


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.FivePath
