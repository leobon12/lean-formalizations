import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.ExcursionPositive
import LQGMetric.Papers.LM.LocEquiv




 





set_option autoImplicit false
noncomputable section
open Set Metric
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

theorem isCompact_closure_exhaustO {V : Set ℂ}
    (hVc : IsCompact (closure V)) (n : ℕ) :
    IsCompact (closure (LQGMetric.LM.exhaustO V n : Set ℂ)) := by
  exact hVc.of_isClosed_subset isClosed_closure
    (closure_mono (LQGMetric.LM.exhaustO_subset V n))

theorem isCompact_closure_exhaustO_ball (z : ℂ) (R : ℝ) (n : ℕ) :
    IsCompact (closure (LQGMetric.LM.exhaustO (Metric.ball z R) n : Set ℂ)) := by
  apply (isCompact_closedBall z R).of_isClosed_subset isClosed_closure
  exact (closure_mono (LQGMetric.LM.exhaustO_subset (Metric.ball z R) n)).trans
    Metric.closure_ball_subset_closedBall

theorem internal_eq_iInf_compact_exhaust (D : LSCMetric)
    (hforget : Continuous (Measurability.SetGeodesicCodes.euclidForget D))
    {V : Set ℂ} (hV : IsOpen V) (hne : Vᶜ.Nonempty)
    (u v : V) :
    D.internal V (u, v) =
      ⨅ n : ℕ, LQGMetric.MetricGeometry.internalEDist
        (D.pt '' closure (LQGMetric.LM.exhaustO V n : Set ℂ))
        (D.pt u) (D.pt v) := by
  rw [LSCMetric.internal_eq_internalEDist]
  refine le_antisymm (le_iInf fun n =>
    LQGMetric.MetricGeometry.internalEDist_anti
      (Set.image_mono ?_) _ _) ?_
  · have hthick := LQGMetric.LM.thickening_closure_exhaustO_subset V n
    exact (subset_trans (self_subset_thickening (by positivity) _)
      hthick)
  · unfold LQGMetric.MetricGeometry.internalEDist
    refine le_iInf fun γ => ?_
    let K : Set ℂ := Set.range (Measurability.SetGeodesicCodes.euclidForget D ∘ γ.1)
    have hKc : IsCompact K := isCompact_range (hforget.comp γ.1.continuous)
    have hKV : K ⊆ V := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨y, hy, hyt⟩ := γ.2 t
      change Measurability.SetGeodesicCodes.euclidForget D (γ.1 t) ∈ V
      rw [← hyt]
      exact hy
    obtain ⟨δ, hδ, hδV⟩ := hKc.exists_thickening_subset_open hV hKV
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    have hKW : K ⊆ LQGMetric.LM.exhaustO V n := by
      intro z hz
      show 1 / ((n : ℝ) + 1) < infDist z Vᶜ
      refine hn.trans_le ((le_infDist hne).2 fun y hy =>
        le_of_not_gt fun hlt => hy ?_)
      exact hδV (mem_thickening_iff.2 ⟨z, hz, by rw [dist_comm]; exact hlt⟩)
    refine iInf_le_of_le n (iInf_le_of_le
      ⟨γ.1, fun t => ⟨Measurability.SetGeodesicCodes.euclidForget D (γ.1 t),
        subset_closure (hKW ⟨t, rfl⟩), rfl⟩⟩ le_rfl)

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
