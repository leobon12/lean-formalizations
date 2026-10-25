import SupercriticalLQGUniqueness.B2.DG20Lim.CircleChainSep
import SupercriticalLQGUniqueness.B2.DG20Lim.ChainLimit

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RatCircle.point_opposite_sides_of_disconnects
    (K P : RatCircle) (z : ℂ)
    (hP : Disjoint P.toSet K.toSet)
    (hsep : K.DisconnectsPoint z P) :
    (z ∈ K.openDisk ∧ P.toSet ⊆ K.closedDiskᶜ) ∨
      (P.toSet ⊆ K.openDisk ∧ z ∈ K.closedDiskᶜ) := by
  by_cases hzi : z ∈ K.openDisk
  · rcases K.side_of_disjoint P hP with hPi | hPo
    · exfalso
      apply hsep.2
      refine ⟨K.openDisk, isPreconnected_ball, ?_, ?_, ?_⟩
      · intro u hu huK
        exact (ne_of_lt (mem_ball.mp hu)) (mem_sphere.mp huK)
      · exact ⟨z, hzi, rfl⟩
      · obtain ⟨p, hp⟩ := P.toSet_nonempty
        exact ⟨p, hPi hp, hp⟩
    · exact Or.inl ⟨hzi, hPo⟩
  · have hzo : z ∈ K.closedDiskᶜ := by
      have hzle : (K.radius : ℝ) ≤ dist z K.center :=
        le_of_not_gt (by simpa only [RatCircle.openDisk, mem_ball] using hzi)
      have hzneq : dist z K.center ≠ (K.radius : ℝ) := by
        intro heq
        exact hsep.1 (mem_sphere.mpr heq)
      simpa only [RatCircle.closedDisk, mem_compl_iff, mem_closedBall, not_le]
        using lt_of_le_of_ne hzle hzneq.symm
    rcases K.side_of_disjoint P hP with hPi | hPo
    · exact Or.inr ⟨hPi, hzo⟩
    · exfalso
      apply hsep.2
      refine ⟨K.closedDiskᶜ, K.isPreconnected_exterior, ?_, ?_, ?_⟩
      · exact compl_subset_compl.mpr K.toSet_subset_closedDisk
      · exact ⟨z, hzo, rfl⟩
      · obtain ⟨p, hp⟩ := P.toSet_nonempty
        exact ⟨p, hPo hp, hp⟩

 

theorem RatCircle.disconnectsPoint_trans
    (K P Q : RatCircle) (z : ℂ)
    (hPK : Disjoint P.toSet K.toSet)
    (hQK : Disjoint Q.toSet K.toSet)
    (hQP : Disjoint Q.toSet P.toSet)
    (hK : K.DisconnectsPoint z P)
    (hP : Disconnects P.toSet K.toSet Q.toSet) :
    K.DisconnectsPoint z Q := by
  have hzP := K.point_opposite_sides_of_disconnects P z hPK hK
  have hKQ := P.opposite_sides_of_disconnects K Q hPK.symm hQP hP
  refine ⟨hK.1, ?_⟩
  rcases hzP with ⟨hzi, hPo⟩ | ⟨hPi, hzo⟩
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
    exact K.disconnects_of_subsets (by simpa using hzi)
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
      (fun o ho hoi => by
        have : o = z := Set.mem_singleton_iff.mp ho
        subst o
        exact hzo (K.openDisk_subset_closedDisk hoi)))

end SupercriticalLQGUniqueness.B2.DG20Lim
