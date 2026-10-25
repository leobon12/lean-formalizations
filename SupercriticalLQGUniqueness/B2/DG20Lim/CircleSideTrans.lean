import SupercriticalLQGUniqueness.B2.DG20Lim.CircleSides

 

set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RatCircle.closedDisk_subset_openDisk_of_circle_subset
    (K O : RatCircle) (h : O.toSet ⊆ K.openDisk) :
    O.closedDisk ⊆ K.openDisk :=
  LQGMetric.TopoCircle.closedBall_subset_ball_of_sphere_subset
    (Rat.cast_nonneg.mpr O.radius_nonneg) h

theorem RatCircle.outer_of_inner (K O : RatCircle)
    (h : O.toSet ⊆ K.openDisk) :
    K.toSet ⊆ O.closedDiskᶜ := by
  have hDisk := K.closedDisk_subset_openDisk_of_circle_subset O h
  intro u huK huO
  exact (ne_of_lt (mem_ball.mp (hDisk huO))) (mem_sphere.mp huK)

 

theorem RatCircle.disjoint_closedDisk_of_mutual_exterior
    (K P : RatCircle)
    (hPK : P.toSet ⊆ K.closedDiskᶜ)
    (hKP : K.toSet ⊆ P.closedDiskᶜ) :
    Disjoint K.closedDisk P.closedDisk := by
  apply disjoint_left.mpr
  intro x hxK hxP
  have hxInner : dist x K.center < (K.radius : ℝ) := by
    have hxLe : dist x K.center ≤ (K.radius : ℝ) := mem_closedBall.mp hxK
    rcases eq_or_lt_of_le hxLe with heq | hlt
    · exfalso
      exact hKP (mem_sphere.mpr heq) hxP
    · exact hlt
  obtain ⟨p, hp⟩ := P.toSet_nonempty
  have hpOuter : (K.radius : ℝ) < dist p K.center := by
    simpa only [RatCircle.closedDisk, mem_compl_iff, mem_closedBall, not_le]
      using hPK hp
  have hval : (K.radius : ℝ) ∈ Icc (dist x K.center) (dist p K.center) :=
    ⟨hxInner.le, hpOuter.le⟩
  have hpre : IsPreconnected P.closedDisk := isPreconnected_closedBall
  obtain ⟨q, hqP, hqK⟩ :=
    hpre.intermediate_value hxP (P.toSet_subset_closedDisk hp)
      ((continuous_id.dist continuous_const).continuousOn) hval
  exact hKP (mem_sphere.mpr hqK) hqP

 

theorem RatCircle.disconnects_trans (K O P Q : RatCircle)
    (hOK : Disjoint O.toSet K.toSet)
    (hPK : Disjoint P.toSet K.toSet)
    (hQK : Disjoint Q.toSet K.toSet)
    (hQP : Disjoint Q.toSet P.toSet)
    (hK : Disconnects K.toSet O.toSet P.toSet)
    (hP : Disconnects P.toSet K.toSet Q.toSet) :
    Disconnects K.toSet O.toSet Q.toSet := by
  have hOP := K.opposite_sides_of_disconnects O P hOK hPK hK
  have hKQ := P.opposite_sides_of_disconnects K Q hPK.symm hQP hP
  rcases hOP with ⟨hOi, hPo⟩ | ⟨hPi, hOo⟩
  · have hQo : Q.toSet ⊆ K.closedDiskᶜ := by
      rcases K.side_of_disjoint Q hQK with hQi | hQo
      · rcases hKQ with ⟨hKi, hQoP⟩ | ⟨hQiP, hKoP⟩
        · obtain ⟨q, hq⟩ := Q.toSet_nonempty
          exact False.elim (hQoP hq
            (P.openDisk_subset_closedDisk
              ((P.closedDisk_subset_openDisk_of_circle_subset K hKi)
                (K.openDisk_subset_closedDisk (hQi hq)))))
        · have hdisj := K.disjoint_closedDisk_of_mutual_exterior P hPo hKoP
          obtain ⟨q, hq⟩ := Q.toSet_nonempty
          exact False.elim ((Set.disjoint_left.mp hdisj)
            (K.openDisk_subset_closedDisk (hQi hq))
            (P.openDisk_subset_closedDisk (hQiP hq)))
      · exact hQo
    exact K.disconnects_of_subsets hOi
      (fun q hq hqi => hQo hq (K.openDisk_subset_closedDisk hqi))
  · have hQi : Q.toSet ⊆ K.openDisk := by
      rcases K.side_of_disjoint Q hQK with hQi | hQo
      · exact hQi
      · rcases hKQ with ⟨hKiP, hQoP⟩ | ⟨hQiP, hKoP⟩
        · have hKo' := K.outer_of_inner P hPi
          obtain ⟨k, hk⟩ := K.toSet_nonempty
          exact False.elim (hKo' hk
            (P.openDisk_subset_closedDisk (hKiP hk)))
        · have hPdisk := K.closedDisk_subset_openDisk_of_circle_subset P hPi
          obtain ⟨q, hq⟩ := Q.toSet_nonempty
          exact False.elim (hQo hq
            (K.openDisk_subset_closedDisk
              (hPdisk (P.openDisk_subset_closedDisk (hQiP hq)))))
    exact disconnects_symm (K.disconnects_of_subsets hQi
      (fun o ho hoi => hOo ho (K.openDisk_subset_closedDisk hoi)))

 

theorem RatCircle.disconnects_trans_right (K O P Q : RatCircle)
    (hOK : Disjoint O.toSet K.toSet)
    (hPK : Disjoint P.toSet K.toSet)
    (hQP : Disjoint Q.toSet P.toSet)
    (hOP : Disjoint O.toSet P.toSet)
    (hK : Disconnects K.toSet O.toSet P.toSet)
    (hP : Disconnects P.toSet K.toSet Q.toSet) :
    Disconnects P.toSet O.toSet Q.toSet := by
  have h := P.disconnects_trans Q K O hQP hPK.symm hOP hOK
    (disconnects_symm hP) (disconnects_symm hK)
  exact disconnects_symm h

end SupercriticalLQGUniqueness.B2.DG20Lim
