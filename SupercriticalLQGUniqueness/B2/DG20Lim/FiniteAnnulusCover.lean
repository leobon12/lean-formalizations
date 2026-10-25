import SupercriticalLQGUniqueness.B2.DG20Lim.PointAnnulusCross
import SupercriticalLQGUniqueness.B2.DG20Lim.RData

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem finite_annulus_cover_of_separated_compact
    {K J : Set ℂ} (hK : IsCompact K)
    {d : ℝ} (hd : 0 < d)
    (hSep : ∀ x ∈ K, ∀ y ∈ J, d ≤ dist x y) :
    ∃ q : Set ℂ, q.Finite ∧ q ⊆ K ∧
      ∀ x ∈ K, ∀ y ∈ J,
        ∃ z ∈ q, dist x z < d / 16 ∧ 3 * d / 4 < dist y z := by
  have hcover : K ⊆ ⋃ z ∈ K, ball z (d / 16) := by
    intro x hx
    exact mem_biUnion hx (mem_ball_self (by positivity))
  obtain ⟨q, hqK, hqFin, hqCover⟩ :=
    hK.elim_finite_subcover_image (fun _ _ => isOpen_ball) hcover
  refine ⟨q, hqFin, hqK, ?_⟩
  intro x hx y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp (hqCover hx)
  obtain ⟨hz, hxz⟩ := mem_iUnion.mp hz
  have hzy : d ≤ dist z y := hSep z (hqK hz) y hy
  refine ⟨z, hz, mem_ball.mp hxz, ?_⟩
  rw [dist_comm y z]
  linarith

 

theorem exists_circle_separation_scale (O P : RatCircle)
    (hOP : Disjoint O.toSet P.toSet) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧
      ∀ u ∈ O.toSet, ∀ v ∈ P.toSet, d ≤ dist u v := by
  have hO : IsCompact O.toSet := isCompact_sphere O.center (O.radius : ℝ)
  have hP : IsCompact P.toSet := isCompact_sphere P.center (P.radius : ℝ)
  have hnO : O.toSet.Nonempty :=
    NormedSpace.sphere_nonempty.mpr (Rat.cast_nonneg.mpr O.radius_nonneg)
  have hnP : P.toSet.Nonempty :=
    NormedSpace.sphere_nonempty.mpr (Rat.cast_nonneg.mpr P.radius_nonneg)
  obtain ⟨p, hp, hmin⟩ :=
    (hO.prod hP).exists_isMinOn (hnO.prod hnP)
      (continuous_fst.dist continuous_snd).continuousOn
  have hne : p.1 ≠ p.2 := by
    intro he
    exact (Set.disjoint_left.mp hOP) hp.1 (he ▸ hp.2)
  have hpos : 0 < dist p.1 p.2 := dist_pos.mpr hne
  let d : ℝ := min (dist p.1 p.2 / 2) (1 / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d, hd, min_le_right _ _, ?_⟩
  intro u hu v hv
  have hle : dist p.1 p.2 ≤ dist u v :=
    hmin (show (u, v) ∈ O.toSet ×ˢ P.toSet from ⟨hu, hv⟩)
  exact (min_le_left _ _).trans (by linarith)

end SupercriticalLQGUniqueness.B2.DG20Lim
