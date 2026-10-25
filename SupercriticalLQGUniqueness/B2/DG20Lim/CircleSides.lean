import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteChainGlobal
import LQGMetric.Topo.CircleUnion
import LQGMetric.Papers.GM.S4.P412eFin

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RatCircle.side_of_disjoint (K O : RatCircle)
    (hdisj : Disjoint O.toSet K.toSet) :
    O.toSet ⊆ K.openDisk ∨ O.toSet ⊆ K.closedDiskᶜ := by
  by_cases hex : ∃ u ∈ O.toSet, u ∈ K.openDisk
  · obtain ⟨u, hu, huIn⟩ := hex
    left
    intro v hv
    by_contra hvIn
    have huv : (K.radius : ℝ) ∈
        Icc (dist u K.center) (dist v K.center) := by
      constructor
      · exact (mem_ball.mp huIn).le
      · exact le_of_not_gt (by simpa only [RatCircle.openDisk, mem_ball] using hvIn)
    obtain ⟨p, hpO, hpK⟩ :=
      (LQGMetric.TopoCircle.isPreconnected_sphere_complex O.center
        (Rat.cast_nonneg.mpr O.radius_nonneg)).intermediate_value
        hu hv ((continuous_id.dist continuous_const).continuousOn) huv
    exact (Set.disjoint_left.mp hdisj) hpO (mem_sphere.mpr hpK)
  · right
    intro v hv
    have hvNotIn : v ∉ K.openDisk := by
      intro h
      exact hex ⟨v, hv, h⟩
    have hvNotSphere : v ∉ K.toSet := by
      intro h
      exact (Set.disjoint_left.mp hdisj) hv h
    have hge : (K.radius : ℝ) ≤ dist v K.center :=
      le_of_not_gt (by simpa only [RatCircle.openDisk, mem_ball] using hvNotIn)
    have hne : dist v K.center ≠ (K.radius : ℝ) := by
      intro heq
      exact hvNotSphere (mem_sphere.mpr heq)
    show v ∈ K.closedDiskᶜ
    simp only [RatCircle.closedDisk, mem_compl_iff, mem_closedBall, not_le]
    exact lt_of_le_of_ne hge hne.symm

theorem RatCircle.isPreconnected_exterior (K : RatCircle) :
    IsPreconnected K.closedDiskᶜ := by
  by_cases hr : K.radius = 0
  · have hball : K.closedDisk = {K.center} := by
      simp [RatCircle.closedDisk, hr]
    rw [hball]
    exact (isConnected_compl_singleton_of_one_lt_rank
      (by simp [Complex.rank_real_complex]) K.center).isPreconnected
  · have hrpos : (0 : ℝ) < (K.radius : ℝ) :=
      Rat.cast_pos.mpr (lt_of_le_of_ne K.radius_nonneg (Ne.symm hr))
    exact LQGMetric.GM.p412e_compl_closedBall_isPreconnected K.center hrpos

theorem RatCircle.toSet_nonempty (O : RatCircle) : O.toSet.Nonempty :=
  NormedSpace.sphere_nonempty.mpr (Rat.cast_nonneg.mpr O.radius_nonneg)

 

theorem RatCircle.opposite_sides_of_disconnects
    (K O P : RatCircle)
    (hO : Disjoint O.toSet K.toSet)
    (hP : Disjoint P.toSet K.toSet)
    (hsep : Disconnects K.toSet O.toSet P.toSet) :
    (O.toSet ⊆ K.openDisk ∧ P.toSet ⊆ K.closedDiskᶜ) ∨
      (P.toSet ⊆ K.openDisk ∧ O.toSet ⊆ K.closedDiskᶜ) := by
  rcases K.side_of_disjoint O hO with hOi | hOo
  · rcases K.side_of_disjoint P hP with hPi | hPo
    · exfalso
      apply hsep
      refine ⟨K.openDisk, isPreconnected_ball, ?_, ?_, ?_⟩
      · intro u hu huK
        exact (ne_of_lt (mem_ball.mp hu)) (mem_sphere.mp huK)
      · obtain ⟨u, hu⟩ := O.toSet_nonempty
        exact ⟨u, hOi hu, hu⟩
      · obtain ⟨u, hu⟩ := P.toSet_nonempty
        exact ⟨u, hPi hu, hu⟩
    · exact Or.inl ⟨hOi, hPo⟩
  · rcases K.side_of_disjoint P hP with hPi | hPo
    · exact Or.inr ⟨hPi, hOo⟩
    · exfalso
      apply hsep
      refine ⟨K.closedDiskᶜ, K.isPreconnected_exterior, ?_, ?_, ?_⟩
      · exact compl_subset_compl.mpr K.toSet_subset_closedDisk
      · obtain ⟨u, hu⟩ := O.toSet_nonempty
        exact ⟨u, hOo hu, hu⟩
      · obtain ⟨u, hu⟩ := P.toSet_nonempty
        exact ⟨u, hPo hu, hu⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
