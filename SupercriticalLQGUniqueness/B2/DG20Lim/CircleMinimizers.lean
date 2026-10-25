import SupercriticalLQGUniqueness.B2.DG20Lim.CircleCrossing

 

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem exists_circleDist_minimizers (D : LQGMetric.ContMetric)
    (O P : RatCircle) :
    ∃ u ∈ O.toSet, ∃ v ∈ P.toSet,
      ENNReal.ofReal (D.1 (u, v)) =
        LQGMetric.Blueprint.setDist D O.toSet P.toSet := by
  have hcO : IsCompact (D.pt '' O.toSet) :=
    (isCompact_sphere O.center (O.radius : ℝ)).image D.continuous_pt
  have hcP : IsCompact (D.pt '' P.toSet) :=
    (isCompact_sphere P.center (P.radius : ℝ)).image D.continuous_pt
  have hnO : (D.pt '' O.toSet).Nonempty :=
    (NormedSpace.sphere_nonempty.mpr
      (Rat.cast_nonneg.mpr O.radius_nonneg)).image D.pt
  have hnP : (D.pt '' P.toSet).Nonempty :=
    (NormedSpace.sphere_nonempty.mpr
      (Rat.cast_nonneg.mpr P.radius_nonneg)).image D.pt
  obtain ⟨u, ⟨u₀, hu₀, rfl⟩, v, ⟨v₀, hv₀, rfl⟩, heq⟩ :=
    LQGMetric.MetricGeometry.IsCompact.exists_setEDist_eq_edist hcO hcP hnO hnP
  refine ⟨u₀, hu₀, v₀, hv₀, ?_⟩
  rw [LQGMetric.ContMetric.edist_pt] at heq
  exact heq.symm

end SupercriticalLQGUniqueness.B2.DG20Lim
