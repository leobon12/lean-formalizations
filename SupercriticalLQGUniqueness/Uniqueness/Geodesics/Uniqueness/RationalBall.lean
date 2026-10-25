import SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness.SetGeoTrace
import LQGMetric.Papers.MQ.SphereCover




 





set_option autoImplicit false
noncomputable section
open Set Metric
namespace SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness

 

theorem exists_rat_ball_avoiding_closed (F : Set ℂ) (hF : IsClosed F)
    (w : ℂ) (hw : w ∉ F) :
    ∃ a b ρ : ℚ, (0 : ℝ) < ρ ∧
      ‖w - (⟨a, b⟩ : ℂ)‖ < ρ ∧
      ∀ z ∈ F, 3 * (ρ : ℝ) ≤ ‖z - (⟨a, b⟩ : ℂ)‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hF.isOpen_compl w hw
  obtain ⟨ρ, hρ0, hρε⟩ := exists_rat_btwn
    (show (0 : ℝ) < ε / 5 by positivity)
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn
    (show w.re - (ρ : ℝ) / 2 < w.re + (ρ : ℝ) / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn
    (show w.im - (ρ : ℝ) / 2 < w.im + (ρ : ℝ) / 2 by linarith)
  have hq : ‖w - (⟨a, b⟩ : ℂ)‖ < ρ := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have hr : |w.re - a| < (ρ : ℝ) / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    have hi : |w.im - b| < (ρ : ℝ) / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith
  have hfar : ∀ z ∈ F, 3 * (ρ : ℝ) ≤ ‖z - (⟨a, b⟩ : ℂ)‖ := by
    intro z hz
    have hzε : ε ≤ ‖z - w‖ := by
      by_contra hlt
      push Not at hlt
      exact hball (by rw [mem_ball, dist_eq_norm]; exact hlt) hz
    have htri := norm_sub_le_norm_sub_add_norm_sub z ⟨a, b⟩ w
    rw [norm_sub_rev (⟨a, b⟩ : ℂ) w] at htri
    linarith
  exact ⟨a, b, ρ, hρ0, hq, hfar⟩

end SupercriticalLQGUniqueness.Uniqueness.Geodesics.Uniqueness
