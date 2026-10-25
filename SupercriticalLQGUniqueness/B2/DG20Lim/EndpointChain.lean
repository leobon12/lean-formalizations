import SupercriticalLQGUniqueness.B2.DG20Lim.PointSideTrans

 


set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem left_endpoint_disconnects_chain
    (k : ℕ) (hk : 0 < k) (O : Fin (k + 1) → RatCircle)
    (z : ℂ)
    (hdisj : ∀ i j : Fin (k + 1), i ≠ j →
      Disjoint (O i).toSet (O j).toSet)
    (hsep : ∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
      Disconnects (O ⟨j, by omega⟩).toSet
        (O ⟨j - 1, by omega⟩).toSet
        (O ⟨j + 1, by omega⟩).toSet)
    (hz : (O ⟨0, by omega⟩).DisconnectsPoint z
      (O ⟨1, by omega⟩)) :
    (O ⟨0, by omega⟩).DisconnectsPoint z
      (O ⟨k, by omega⟩) := by
  have hD (a b : ℕ) (ha : a ≤ k) (hb : b ≤ k) (hab : a ≠ b) :
      Disjoint (O ⟨a, by omega⟩).toSet (O ⟨b, by omega⟩).toSet := by
    apply hdisj
    intro heq
    exact hab (congrArg Fin.val heq)
  have hglobal := circle_chain_global_separator k O hdisj hsep
  have hprop : ∀ j : ℕ, (hj : 0 < j) → (hjk : j ≤ k) →
      (O ⟨0, by omega⟩).DisconnectsPoint z (O ⟨j, by omega⟩) := by
    intro j
    induction j with
    | zero =>
        intro hj
        omega
    | succ j ih =>
        intro hj hjk
        by_cases hj0 : j = 0
        · subst j
          simpa only [Nat.succ_eq_add_one, Nat.zero_add] using hz
        · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
          have hprev := ih hjpos (by omega : j ≤ k)
          have hnext : (O ⟨0, by omega⟩).DisconnectsPoint z
              (O ⟨j + 1, by omega⟩) :=
            (O ⟨0, by omega⟩).disconnectsPoint_trans
            (O ⟨j, by omega⟩) (O ⟨j + 1, by omega⟩) z
            (hD j 0 (by omega) (by omega) (by omega))
            (hD (j + 1) 0 (by omega) (by omega) (by omega))
            (hD (j + 1) j (by omega) (by omega) (by omega))
            hprev (hglobal j hjpos (by omega))
          simpa only [Nat.succ_eq_add_one] using hnext
  exact hprop k hk le_rfl

end SupercriticalLQGUniqueness.B2.DG20Lim
