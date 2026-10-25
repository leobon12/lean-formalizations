import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteGoodCoupledLimit

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def sparseDyadicIndices (K : ℕ) : Finset ℕ :=
  Finset.Icc (K / 12 + 1) (K / 6)

theorem sparseDyadicIndices_nonempty {K : ℕ} (hK : 12 ≤ K) :
    (sparseDyadicIndices K).Nonempty := by
  have hle : K / 12 + 1 ≤ K / 6 := by omega
  exact ⟨K / 12 + 1, Finset.mem_Icc.mpr ⟨le_refl _, hle⟩⟩

theorem sparseDyadicIndices_scale {K i : ℕ}
    (hi : i ∈ sparseDyadicIndices K) :
    K ≤ 2 * (6 * i) ∧ 6 * i ≤ K := by
  have hi' := Finset.mem_Icc.mp hi
  omega

theorem sparseDyadicIndices_card {K : ℕ} (hK : 12 ≤ K) :
    (sparseDyadicIndices K).card = K / 6 - K / 12 := by
  have hle : K / 12 + 1 ≤ K / 6 := by omega
  simp only [sparseDyadicIndices, Nat.card_Icc]
  omega

theorem sparseDyadicIndices_card_lower {K : ℕ} (hK : 12 ≤ K) :
    K ≤ 24 * (sparseDyadicIndices K).card := by
  rw [sparseDyadicIndices_card hK]
  omega

end SupercriticalLQGUniqueness.B2.DG20Lim
