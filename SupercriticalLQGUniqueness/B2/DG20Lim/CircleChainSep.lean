import SupercriticalLQGUniqueness.B2.DG20Lim.CircleSideTrans

 


set_option autoImplicit false
noncomputable section

open Set

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem circle_chain_global_separator (k : ℕ)
    (O : Fin (k + 1) → RatCircle)
    (hdisj : ∀ i j : Fin (k + 1), i ≠ j →
      Disjoint (O i).toSet (O j).toSet)
    (hsep : ∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
      Disconnects (O ⟨j, by omega⟩).toSet
        (O ⟨j - 1, by omega⟩).toSet
        (O ⟨j + 1, by omega⟩).toSet) :
    ∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
      Disconnects (O ⟨j, by omega⟩).toSet
        (O ⟨0, by omega⟩).toSet
        (O ⟨j + 1, by omega⟩).toSet := by
  have hD (a b : ℕ) (ha : a ≤ k) (hb : b ≤ k) (hab : a ≠ b) :
      Disjoint (O ⟨a, by omega⟩).toSet (O ⟨b, by omega⟩).toSet := by
    apply hdisj
    intro heq
    exact hab (congrArg Fin.val heq)
  intro j
  induction j with
  | zero =>
      intro hj
      omega
  | succ j ih =>
      intro hj hjk
      by_cases hj0 : j = 0
      · subst j
        simpa only [Nat.zero_add, Nat.zero_sub, Nat.succ_eq_add_one]
          using hsep 1 (by omega) (by omega)
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        have hprev := ih hjpos (by omega : j < k)
        have hlocal := hsep (j + 1) (by omega) hjk
        have hnext := RatCircle.disconnects_trans_right
          (O ⟨j, by omega⟩) (O ⟨0, by omega⟩)
          (O ⟨j + 1, by omega⟩) (O ⟨j + 2, by omega⟩)
          (hD 0 j (by omega) (by omega) (by omega))
          (hD (j + 1) j (by omega) (by omega) (by omega))
          (hD (j + 2) (j + 1) (by omega) (by omega) (by omega))
          (hD 0 (j + 1) (by omega) (by omega) (by omega))
          hprev (by simpa [Nat.add_sub_cancel_right, Nat.add_assoc] using hlocal)
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hnext

end SupercriticalLQGUniqueness.B2.DG20Lim
