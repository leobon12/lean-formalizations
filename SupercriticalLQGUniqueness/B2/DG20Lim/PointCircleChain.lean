import SupercriticalLQGUniqueness.B2.DG20Lim.NestedFourChain
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalUpper

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.across_inner_outer_le_endpoint
    (R : RData) (Z O Q : RatCircle)
    (hZO : O.SurroundsCircle Z)
    (hOQ : Disjoint O.closedDisk Q.toSet) :
    R.across Z O ≤ R.across Z Q := by
  have hZOdisj : Disjoint Z.toSet O.toSet :=
    RatCircle.disjoint_of_nested hZO
  have hOQdisj : Disjoint O.toSet Q.toSet :=
    hOQ.mono O.toSet_subset_closedDisk Subset.rfl
  have hZQdisj : Disjoint Z.toSet Q.toSet :=
    hOQ.mono
      (Z.toSet_subset_closedDisk.trans
        (hZO.2.trans O.openDisk_subset_closedDisk))
      Subset.rfl
  let A : Fin 3 → RatCircle := ![Z, O, Q]
  have hdisj : ∀ i j : Fin 3, i ≠ j →
      Disjoint (A i).toSet (A j).toSet := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [A, disjoint_comm]
  have hsep : ∀ j : ℕ, (hj : 0 < j) → (hjk : j < 2) →
      Disconnects (A ⟨j, by omega⟩).toSet
        (A ⟨j - 1, by omega⟩).toSet
        (A ⟨j + 1, by omega⟩).toSet := by
    intro j hj hjk
    have hj' : j = 1 := by omega
    subst j
    change Disconnects O.toSet Z.toSet Q.toSet
    apply O.disconnects_of_subsets
    · exact Z.toSet_subset_closedDisk.trans hZO.2
    · intro u huQ huO
      exact (disjoint_left.mp hOQ)
        (O.openDisk_subset_closedDisk huO)
        huQ
  have hchain := R.chain_lower 2 A hdisj hsep
  have hchain' : R.across Z O + R.across O Q ≤ R.across Z Q := by
    simpa [A, Fin.sum_univ_succ] using hchain
  exact (le_add_of_nonneg_right zero_le).trans hchain'

theorem RData.across_point_circle_le_point
    (R : RData) (Z O Q : RatCircle)
    (hZ : Z.radius = 0) (hQ : Q.radius = 0)
    (hO : O.Surrounds Z.center)
    (hQout : Q.center ∉ O.closedDisk) :
    R.across Z O ≤ R.across Z Q := by
  apply R.across_inner_outer_le_endpoint Z O Q
    (O.surroundsCircle_zero Z hZ hO)
  rw [Q.toSet_eq_singleton_of_radius_zero hQ]
  apply disjoint_singleton_right.mpr
  exact hQout

end SupercriticalLQGUniqueness.B2.DG20Lim
