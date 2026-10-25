import SupercriticalLQGUniqueness.Uniqueness.Objects.Tube.Loc




 












set_option autoImplicit false

noncomputable section

open Complex Set Metric Real

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Tube

namespace TubeParams

variable (P : TubeParams) (r Asup : ℝ)

 
def βu (k : ℤ) : Set ℂ := ball (P.uC r k) (P.s r + Asup * r)

 
def βv (k : ℤ) : Set ℂ := ball (P.vC r k) (P.s r + Asup * r)

 
def Ob (k : ℤ) : Set ℂ := thickening (Asup * r) (P.block r k) \ (P.βu r Asup k ∪ P.βv r Asup k)

 
def Λc (k : ℤ) : Set ℂ :=
  thickening (P.w r + Asup * r) (P.conn r k) \ (P.βv r Asup k ∪ P.βu r Asup (k + 1))

 
def piece (k : ℤ) : ℕ → Set ℂ
  | 0 => P.βu r Asup k
  | 1 => P.Ob r Asup k
  | 2 => P.βv r Asup k
  | _ => P.Λc r Asup k

 
def X (i : ℤ) : Set ℂ := P.piece r Asup (i / 4) (i % 4).toNat

theorem X_four_mul_add (k : ℤ) (a : ℕ) (ha : a < 4) : P.X r Asup (4 * k + a) = P.piece r Asup k a := by
  unfold X
  have h1 : (4 * k + (a : ℤ)) / 4 = k := by omega
  have h2 : ((4 * k + (a : ℤ)) % 4).toNat = a := by omega
  rw [h1, h2]

 

variable {P r Asup}

theorem nbhd_eq_iUnion_X (hs : 0 < P.s r) (hw : 0 < P.w r) (ha : 0 < Asup * r) :
    P.nbhd r Asup = ⋃ i : ℤ, P.X r Asup i := by
  unfold nbhd tube
  rw [thickening_iUnion]
  simp only [thickening_union, thickening_ball ha hs, thickening_thickening ha hw]
  apply Subset.antisymm
  · intro x hx
    rw [mem_iUnion] at hx ⊢
    obtain ⟨k, hx⟩ := hx
    rcases hx with ((hx | hx) | hx) | hx
    · by_cases h1 : x ∈ P.βu r Asup k
      · exact ⟨4 * k + (0 : ℕ), by rw [X_four_mul_add _ _ _ _ _ (by norm_num)]; exact h1⟩
      by_cases h2 : x ∈ P.βv r Asup k
      · exact ⟨4 * k + (2 : ℕ), by rw [X_four_mul_add _ _ _ _ _ (by norm_num)]; exact h2⟩
      refine ⟨4 * k + (1 : ℕ), ?_⟩
      rw [X_four_mul_add _ _ _ _ _ (by norm_num)]
      exact ⟨hx, by rintro (h | h) <;> contradiction⟩
    · refine ⟨4 * k + (0 : ℕ), ?_⟩
      rw [X_four_mul_add _ _ _ _ _ (by norm_num)]
      show x ∈ ball (P.uC r k) (P.s r + Asup * r)
      rwa [add_comm]
    · refine ⟨4 * k + (2 : ℕ), ?_⟩
      rw [X_four_mul_add _ _ _ _ _ (by norm_num)]
      show x ∈ ball (P.vC r k) (P.s r + Asup * r)
      rwa [add_comm]
    · by_cases h1 : x ∈ P.βv r Asup k
      · exact ⟨4 * k + (2 : ℕ), by rw [X_four_mul_add _ _ _ _ _ (by norm_num)]; exact h1⟩
      by_cases h2 : x ∈ P.βu r Asup (k + 1)
      · refine ⟨4 * (k + 1) + (0 : ℕ), ?_⟩
        rw [X_four_mul_add _ _ _ _ _ (by norm_num)]; exact h2
      refine ⟨4 * k + (3 : ℕ), ?_⟩
      rw [X_four_mul_add _ _ _ _ _ (by norm_num)]
      refine ⟨by rwa [add_comm], ?_⟩
      rintro (h | h) <;> contradiction
  · intro x hx
    rw [mem_iUnion] at hx ⊢
    obtain ⟨i, hx⟩ := hx
    refine ⟨i / 4, ?_⟩
    unfold X at hx
    have hlt : (i % 4).toNat < 4 := by omega
    generalize (i % 4).toNat = a at hx hlt
    interval_cases a
    · change x ∈ ball (P.uC r (i / 4)) (P.s r + Asup * r) at hx
      exact Or.inl (Or.inl (Or.inr (by rwa [add_comm])))
    · change x ∈ P.Ob r Asup (i / 4) at hx
      exact Or.inl (Or.inl (Or.inl hx.1))
    · change x ∈ ball (P.vC r (i / 4)) (P.s r + Asup * r) at hx
      exact Or.inl (Or.inr (by rwa [add_comm]))
    · change x ∈ P.Λc r Asup (i / 4) at hx
      exact Or.inr (by rw [add_comm]; exact hx.1)

end TubeParams

end SupercriticalLQGUniqueness.Uniqueness.Objects.Tube
