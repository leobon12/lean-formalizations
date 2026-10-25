import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.FiniteMaximalV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingCore.Section4Counting




 






set_option autoImplicit false
noncomputable section
open Finset
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym

 

theorem finite_good_family_card
    {α : Type} [DecidableEq α]
    (S Z₀ : Finset α) (N : α → Finset α) (good : α → Prop)
    (𝓕 : Finset (Finset α)) (R M : ℕ)
    (hZ₀ : Z₀ ⊆ S)
    (hself : ∀ x ∈ S, x ∈ N x)
    (hsymm : ∀ x y : α, x ∈ N y ↔ y ∈ N x)
    (hN : ∀ a ∈ S, (N a).card ≤ R)
    (hfamily : ∀ Z ∈ 𝓕, Z ⊆ S ∧ ∀ x ∈ Z, good x)
    (hold : ∀ Z₁ : Finset α, Z₁ ⊆ S →
      (∀ x ∈ Z₁, good x ∧ ∀ a ∈ Z₀, x ∉ N a) →
      (∀ x ∈ Z₁, ∀ y ∈ Z₁, x ≠ y → x ∉ N y) →
      Z₁.card ≤ M * Z₀.card) :
    𝓕.card ≤ 2 ^ (R * ((M + 1) * Z₀.card)) := by
  obtain ⟨Z₁, hZ₁, hgood, hsep, hcover⟩ :=
    exists_maximal_good_separated S Z₀ N good hself hsymm
  have hcount := hold Z₁ hZ₁ hgood hsep
  have hNall : ∀ a ∈ Z₀ ∪ Z₁, (N a).card ≤ R := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha₀ | ha₁
    · exact hN a (hZ₀ ha₀)
    · exact hN a (hZ₁ ha₁)
  have hcoverall : ∀ Z ∈ 𝓕, ∀ x ∈ Z,
      ∃ a ∈ Z₀ ∪ Z₁, x ∈ N a := by
    intro Z hF x hx
    exact hcover x ((hfamily Z hF).1 hx) ((hfamily Z hF).2 x hx)
  have hbase := EndSaving.CountingCore.finiteNeighbor_configuration_count
    (Z₀ ∪ Z₁) N 𝓕 R hNall hcoverall
  have hA : (Z₀ ∪ Z₁).card ≤ (M + 1) * Z₀.card := by
    calc
      (Z₀ ∪ Z₁).card ≤ Z₀.card + Z₁.card := Finset.card_union_le Z₀ Z₁
      _ ≤ Z₀.card + M * Z₀.card := Nat.add_le_add_left hcount _
      _ = (M + 1) * Z₀.card := by
        simp only [Nat.add_mul, one_mul]
        omega
  exact hbase.trans (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left R hA))

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym
