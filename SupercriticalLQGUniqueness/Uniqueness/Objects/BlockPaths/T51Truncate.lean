import LQGMetric.Topo.RectCross




 






set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockPaths

 

theorem first_outer_last_inner_closed_annulus
    {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b))
    {c : ℂ} {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂)
    (ha : ‖P a - c‖ ≤ r₁) (hb : r₂ ≤ ‖P b - c‖) :
    ∃ s t : ℝ, a ≤ s ∧ s ≤ t ∧ t ≤ b ∧
      P s ∈ sphere c r₁ ∧ P t ∈ sphere c r₂ ∧
      MapsTo P (Icc s t)
        (closedBall c r₂ \ ball c r₁) := by
  have hf : ContinuousOn (fun u => ‖P u - c‖) (Icc a b) :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).comp_continuousOn hP
  obtain ⟨s, t, has, hst, htb, hs, ht, hmid⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hab hf hr ha hb
  refine ⟨s, t, has, hst, htb, ?_, ?_, ?_⟩
  · exact mem_sphere_iff_norm.mpr hs
  · exact mem_sphere_iff_norm.mpr ht
  · intro u hu
    have h := hmid u hu
    exact ⟨Metric.mem_closedBall.mpr (by simpa only [dist_eq_norm] using h.2),
      fun hball => (not_lt_of_ge h.1) (by simpa only [mem_ball, dist_eq_norm] using hball)⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockPaths
