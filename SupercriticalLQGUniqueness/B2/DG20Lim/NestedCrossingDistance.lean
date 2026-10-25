import SupercriticalLQGUniqueness.B2.DG20Lim.NestedCrossingSum

 

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.nested_crossing_sum_le_DfromR
    (R : RData) (B : ℕ → RatAnnulus)
    (hnest : ∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer)
    (z w : ℂ) (hzw : z ≠ w)
    (hz : ∀ n, (B n).inner.Surrounds z)
    (hw : w ∉ (B 0).outer.closedDisk)
    (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
      R.across (B n).inner (B n).outer) ≤ R.DfromR z w := by
  let I := (B N).inner
  let O := (B 0).outer
  have hOI : O.SurroundsCircle I :=
    nested_annulus_outer_surrounds_later_inner B hnest N
  have hdisj : Disjoint I.toSet O.toSet := RatCircle.disjoint_of_nested hOI
  have hzi : I.DisconnectsPoint z O := by
    refine ⟨?_, ?_⟩
    · intro hzI
      exact (ne_of_lt (mem_ball.mp (hz N).2)) (mem_sphere.mp hzI)
    · apply I.disconnects_of_subsets
      · intro u hu
        simpa only [mem_singleton_iff] using hu ▸ (hz N).2
      · intro u huO huI
        have huIn : u ∈ O.openDisk := hOI.2 (I.openDisk_subset_closedDisk huI)
        exact (ne_of_lt (mem_ball.mp huIn)) (mem_sphere.mp huO)
  have hwo : O.DisconnectsPoint w I := by
    refine ⟨?_, ?_⟩
    · exact fun hwO => hw (O.toSet_subset_closedDisk hwO)
    · apply disconnects_symm
      apply O.disconnects_of_subsets
      · exact I.toSet_subset_closedDisk.trans hOI.2
      · intro u huW huO
        have huw : u = w := by simpa only [mem_singleton_iff] using huW
        exact hw (huw ▸ O.openDisk_subset_closedDisk huO)
  exact (R.nested_crossing_sum_le_across B hnest N).trans
    (R.across_le_DfromR_of_two_circle_chain I O z w hzw hdisj hzi hwo)

end SupercriticalLQGUniqueness.B2.DG20Lim
