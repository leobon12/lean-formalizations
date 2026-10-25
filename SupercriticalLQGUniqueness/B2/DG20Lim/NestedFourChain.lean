import SupercriticalLQGUniqueness.B2.DG20Lim.NestedAnnulusOuterOrder
import SupercriticalLQGUniqueness.B2.DG20Lim.ChainSource

 

set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.two_edge_sum_le_across_of_nested
    (R : RData) (a b c d : RatCircle)
    (hba : b.SurroundsCircle a)
    (hcb : c.SurroundsCircle b)
    (hdc : d.SurroundsCircle c) :
    R.across a b + R.across c d ≤ R.across a d := by
  have hab : Disjoint a.toSet b.toSet := RatCircle.disjoint_of_nested hba
  have hbc : Disjoint b.toSet c.toSet := RatCircle.disjoint_of_nested hcb
  have hcd : Disjoint c.toSet d.toSet := RatCircle.disjoint_of_nested hdc
  have hac : Disjoint a.toSet c.toSet :=
    RatCircle.disjoint_of_nested (hcb.trans hba)
  have hbd : Disjoint b.toSet d.toSet :=
    RatCircle.disjoint_of_nested (hdc.trans hcb)
  have had : Disjoint a.toSet d.toSet :=
    RatCircle.disjoint_of_nested (hdc.trans (hcb.trans hba))
  let O : Fin 4 → RatCircle := ![a, b, c, d]
  have hdisj : ∀ i j : Fin 4, i ≠ j →
      Disjoint (O i).toSet (O j).toSet := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [O, disjoint_comm]
  have hsep : ∀ j : ℕ, (hj : 0 < j) → (hjk : j < 3) →
      Disconnects (O ⟨j, by omega⟩).toSet
        (O ⟨j - 1, by omega⟩).toSet
        (O ⟨j + 1, by omega⟩).toSet := by
    intro j hj hjk
    have hj' : j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl
    · change Disconnects b.toSet a.toSet c.toSet
      apply b.disconnects_of_subsets
      · exact a.toSet_subset_closedDisk.trans hba.2
      · intro z hzC hzB
        have hzIn : z ∈ c.openDisk := hcb.2 (b.openDisk_subset_closedDisk hzB)
        exact (ne_of_lt (mem_ball.mp hzIn)) (mem_sphere.mp hzC)
    · change Disconnects c.toSet b.toSet d.toSet
      apply c.disconnects_of_subsets
      · exact b.toSet_subset_closedDisk.trans hcb.2
      · intro z hzD hzC
        have hzIn : z ∈ d.openDisk := hdc.2 (c.openDisk_subset_closedDisk hzC)
        exact (ne_of_lt (mem_ball.mp hzIn)) (mem_sphere.mp hzD)
  have hchain := R.chain_lower 3 O hdisj hsep
  have hchain' : R.across a b + R.across b c + R.across c d ≤ R.across a d := by
    simpa [O, Fin.sum_univ_succ, add_assoc] using hchain
  calc
    R.across a b + R.across c d ≤
        R.across a b + R.across b c + R.across c d := by
          have hgap : R.across c d ≤ R.across b c + R.across c d :=
            le_add_of_nonneg_left (show 0 ≤ R.across b c from zero_le)
          simpa only [add_assoc] using add_le_add_right hgap (R.across a b)
    _ ≤ R.across a d := hchain'

end SupercriticalLQGUniqueness.B2.DG20Lim
