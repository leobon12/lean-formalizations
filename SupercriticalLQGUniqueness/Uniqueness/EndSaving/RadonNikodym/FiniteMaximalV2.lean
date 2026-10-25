import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.RemoteBumpV2
import Mathlib.Data.Finset.Max




 





set_option autoImplicit false
noncomputable section
open Finset
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym

 

theorem exists_maximal_good_separated
    {α : Type} [DecidableEq α] (S Z₀ : Finset α)
    (N : α → Finset α) (good : α → Prop)
    (hself : ∀ x ∈ S, x ∈ N x)
    (hsymm : ∀ x y : α, x ∈ N y ↔ y ∈ N x) :
    ∃ Z₁ : Finset α,
      Z₁ ⊆ S ∧
      (∀ x ∈ Z₁, good x ∧ ∀ a ∈ Z₀, x ∉ N a) ∧
      (∀ x ∈ Z₁, ∀ y ∈ Z₁, x ≠ y → x ∉ N y) ∧
      (∀ x ∈ S, good x → ∃ a ∈ Z₀ ∪ Z₁, x ∈ N a) := by
  classical
  let admissible : Finset α → Prop := fun W =>
    W ⊆ S ∧
    (∀ x ∈ W, good x ∧ ∀ a ∈ Z₀, x ∉ N a) ∧
    (∀ x ∈ W, ∀ y ∈ W, x ≠ y → x ∉ N y)
  let cand : Finset (Finset α) := S.powerset.filter admissible
  have hne : cand.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
      (Finset.empty_subset S), ?_⟩⟩
    exact ⟨Finset.empty_subset S, by simp, by simp⟩
  obtain ⟨Z₁, hZ₁, hmax⟩ := Finset.exists_max_image cand Finset.card hne
  obtain ⟨hsub, hgood, hsep⟩ := (Finset.mem_filter.mp hZ₁).2
  refine ⟨Z₁, hsub, hgood, hsep, ?_⟩
  intro x hxS hxgood
  by_contra hcover
  have hfar₀ : ∀ a ∈ Z₀, x ∉ N a := by
    intro a ha hxa
    exact hcover ⟨a, Finset.mem_union_left Z₁ ha, hxa⟩
  have hfar₁ : ∀ a ∈ Z₁, x ∉ N a := by
    intro a ha hxa
    exact hcover ⟨a, Finset.mem_union_right Z₀ ha, hxa⟩
  have hxnot : x ∉ Z₁ := by
    intro hx
    exact hfar₁ x hx (hself x (hsub hx))
  have hnew : insert x Z₁ ∈ cand := by
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr (Finset.insert_subset hxS hsub)
    · refine ⟨Finset.insert_subset hxS hsub, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact ⟨hxgood, hfar₀⟩
        · exact hgood y hy
      · intro p hp q hq hpq
        rcases Finset.mem_insert.mp hp with rfl | hpZ
        · rcases Finset.mem_insert.mp hq with hqx | hqZ
          · exact (hpq hqx.symm).elim
          · exact hfar₁ q hqZ
        · rcases Finset.mem_insert.mp hq with hqx | hqZ
          · subst q
            intro hpN
            exact hfar₁ p hpZ ((hsymm p x).mp hpN)
          · exact hsep p hpZ q hqZ hpq
  have hcard : Z₁.card < (insert x Z₁).card := by
    simp only [Finset.card_insert_of_notMem hxnot]
    omega
  exact (not_le_of_gt hcard) (hmax (insert x Z₁) hnew)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
