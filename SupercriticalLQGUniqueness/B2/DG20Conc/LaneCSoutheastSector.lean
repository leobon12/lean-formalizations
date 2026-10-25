import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerPaidLoop

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric.DDDF

 

theorem laneC_exp_southeast {w : ℂ}
    (hlo : 3 * Real.pi / 2 ≤ w.im) (hhi : w.im ≤ 2 * Real.pi) :
    0 ≤ (Complex.exp w).re ∧ (Complex.exp w).im ≤ 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hθ : -(Real.pi / 2) ≤ w.im - 2 * Real.pi ∧
      w.im - 2 * Real.pi ≤ 0 := by
    constructor <;> linarith
  have hc : 0 ≤ Real.cos w.im := by
    rw [← Real.cos_sub_two_pi w.im]
    exact Real.cos_nonneg_of_mem_Icc ⟨hθ.1, by linarith⟩
  have hs : Real.sin w.im ≤ 0 := by
    rw [← Real.sin_sub_two_pi w.im]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ.2 (by linarith)
  rw [Complex.exp_re, Complex.exp_im]
  exact ⟨mul_nonneg (Real.exp_pos _).le hc,
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hs⟩

 
theorem laneC_exp_lower_half {w : ℂ}
    (hlo : Real.pi ≤ w.im) (hhi : w.im ≤ 2 * Real.pi) :
    (Complex.exp w).im ≤ 0 := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hθ : -Real.pi ≤ w.im - 2 * Real.pi ∧
      w.im - 2 * Real.pi ≤ 0 := by
    constructor <;> linarith
  have hs : Real.sin w.im ≤ 0 := by
    rw [← Real.sin_sub_two_pi w.im]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ.2 hθ.1
  rw [Complex.exp_im]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hs

 
theorem laneC_exp_right_half {w : ℂ}
    (hlo : 3 * Real.pi / 2 ≤ w.im)
    (hhi : w.im ≤ 5 * Real.pi / 2) :
    0 ≤ (Complex.exp w).re := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hθ : -(Real.pi / 2) ≤ w.im - 2 * Real.pi ∧
      w.im - 2 * Real.pi ≤ Real.pi / 2 := by
    constructor <;> linarith
  have hc : 0 ≤ Real.cos w.im := by
    rw [← Real.cos_sub_two_pi w.im]
    exact Real.cos_nonneg_of_mem_Icc hθ
  rw [Complex.exp_re]
  exact mul_nonneg (Real.exp_pos _).le hc

 

theorem laneC_west_point_left {z c w : ℂ} {r : ℝ}
    (hlog : Complex.exp w = z - c) (hangle : w.im = Real.pi)
    (hr : r < dist z c) (hc : c.re ≤ r) : (z).re < 0 := by
  have hnorm : r < Real.exp w.re := by
    simpa [dist_eq_norm, ← hlog, Complex.norm_exp] using hr
  have hwest : (z - c).re = -Real.exp w.re := by
    rw [← hlog, Complex.exp_re, hangle, Real.cos_pi]
    ring
  rw [Complex.sub_re] at hwest
  linarith

 

theorem laneC_north_point_above {z c w : ℂ} {r : ℝ}
    (hlog : Complex.exp w = z - c)
    (hangle : w.im = 5 * Real.pi / 2)
    (hr : r < dist z c) (hc : 1 - c.im ≤ r) : 1 < z.im := by
  have hnorm : r < Real.exp w.re := by
    simpa [dist_eq_norm, ← hlog, Complex.norm_exp] using hr
  have hnorth : (z - c).im = Real.exp w.re := by
    rw [← hlog, Complex.exp_im, hangle,
      show (5 : ℝ) * Real.pi / 2 = Real.pi / 2 + 2 * Real.pi by ring,
      Real.sin_add_two_pi, Real.sin_pi_div_two]
    ring
  rw [Complex.sub_im] at hnorth
  linarith

 

theorem laneC_southeast_sector_in_square
    {c z w : ℂ} {r : ℝ}
    (hlog : Complex.exp w = z - c)
    (hlo : 3 * Real.pi / 2 ≤ w.im) (hhi : w.im ≤ 2 * Real.pi)
    (hcre : 0 ≤ c.re) (hcim : c.im ≤ 1)
    (hbelow : 2 * r ≤ c.im) (hright : c.re + 2 * r ≤ 1)
    (hz : dist z c < 2 * r) :
    z ∈ (rectAB 1 1).toSet := by
  obtain ⟨hx, hy⟩ := laneC_exp_southeast hlo hhi
  rw [hlog, Complex.sub_re] at hx
  rw [hlog, Complex.sub_im] at hy
  have hcoord := Complex.abs_re_le_norm (z - c)
  have hcoord' := Complex.abs_im_le_norm (z - c)
  simp only [Complex.sub_re] at hcoord
  simp only [Complex.sub_im] at hcoord'
  have hnorm : ‖z - c‖ < 2 * r := by simpa [dist_eq_norm] using hz
  have hre : z.re ≤ c.re + 2 * r := by
    have := (abs_le.mp hcoord).2
    linarith
  have him : c.im - 2 * r ≤ z.im := by
    have := (abs_le.mp hcoord').1
    linarith
  rw [mem_rectAB_toSet]
  constructor <;> constructor <;> linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
