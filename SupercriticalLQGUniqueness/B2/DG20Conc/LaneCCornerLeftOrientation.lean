import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSoutheastSector

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_left_contact_below_center
    {z c w : ℂ} {r : ℝ}
    (hlog : Complex.exp w = z - c)
    (hangle : Real.pi ≤ w.im ∧ w.im ≤ 5 * Real.pi / 2)
    (hleft : z.re = 0) (hbelowTop : z.im ≤ 1)
    (hc0 : 0 ≤ c.re) (hTopNear : 1 - c.im ≤ r)
    (hinner : r < dist z c) :
    z.im ≤ c.im := by
  by_contra h
  have hy : c.im < z.im := lt_of_not_ge h
  have hπ : 0 < Real.pi := Real.pi_pos
  have hgt : 2 * Real.pi < w.im := by
    by_contra hle
    have hs := laneC_exp_lower_half hangle.1 (le_of_not_gt hle)
    rw [hlog, Complex.sub_im] at hs
    linarith
  have hle : w.im ≤ 5 * Real.pi / 2 := hangle.2
  have he : (Complex.exp w).re = -c.re := by
    rw [hlog, Complex.sub_re, hleft]
    ring
  have hnotlt : ¬ w.im < 5 * Real.pi / 2 := by
    intro hlt
    have hc : 0 < Real.cos (w.im - 2 * Real.pi) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hc' : 0 < Real.cos w.im := by
      rwa [Real.cos_sub_two_pi] at hc
    have hpos : 0 < (Complex.exp w).re := by
      rw [Complex.exp_re]
      exact mul_pos (Real.exp_pos _) hc'
    linarith
  have hend : w.im = 5 * Real.pi / 2 := le_antisymm hle (le_of_not_gt hnotlt)
  have hnorth := laneC_north_point_above hlog hend hinner hTopNear
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
