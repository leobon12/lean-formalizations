import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteChainTwo

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem finiteCircleDist_chain_of_global_sep
    (D : LQGMetric.ContMetric) (hD : D.IsLength)
    (O : ℕ → RatCircle) (k : ℕ)
    (hsep : ∀ j, 0 < j → j < k →
      Disconnects (O j).toSet (O 0).toSet (O (j + 1)).toSet) :
    (∑ j ∈ Finset.range k,
      LQGMetric.Blueprint.setDist D (O j).toSet (O (j + 1)).toSet) ≤
      LQGMetric.Blueprint.setDist D (O 0).toSet (O k).toSet := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hk : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hsep' : ∀ j, 0 < j → j < k →
          Disconnects (O j).toSet (O 0).toSet (O (j + 1)).toSet := by
        intro j hj hjk
        exact hsep j hj (Nat.lt_succ_of_lt hjk)
      have htwo := finiteCircleDist_two_chain D hD
        (O 0) (O k) (O (k + 1)) (hsep k hkpos (Nat.lt_succ_self k))
      exact (add_le_add_left (ih hsep') _).trans htwo

end SupercriticalLQGUniqueness.B2.DG20Lim
