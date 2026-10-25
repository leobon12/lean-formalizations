import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting.GridNeighbor
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.RadonNikodym.FiniteCardV2




 
set_option autoImplicit false
noncomputable section
open Set Finset
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting

 

theorem uniform_family_count
    {α : Type} [DecidableEq α]
    (eligible : Finset α → Prop) (Z₀ : Finset α)
    (N : α → Finset α) (good : α → Prop) (R M : ℕ)
    (hself : ∀ x : α, x ∈ N x)
    (hsymm : ∀ x y : α, x ∈ N y ↔ y ∈ N x)
    (hN : ∀ x : α, (N x).card ≤ R)
    (hgood : ∀ Z : Finset α, eligible Z → ∀ x ∈ Z, good x)
    (hcount : ∀ Z₁ : Finset α,
      (∀ x ∈ Z₁, good x ∧ ∀ a ∈ Z₀, x ∉ N a) →
      (∀ x ∈ Z₁, ∀ y ∈ Z₁, x ≠ y → x ∉ N y) →
      Z₁.card ≤ M * Z₀.card) :
    let family : Set (Finset α) := {Z | eligible Z}
    family.Finite ∧ family.ncard ≤ 2 ^ (R * ((M + 1) * Z₀.card)) := by
  classical
  dsimp only
  let family : Set (Finset α) := {Z | eligible Z}
  let B := 2 ^ (R * ((M + 1) * Z₀.card))
  have hfiniteBound : ∀ 𝓕 : Finset (Finset α), (𝓕 : Set (Finset α)) ⊆ family →
      𝓕.card ≤ B := by
    intro 𝓕 h𝓕
    let S := Z₀ ∪ 𝓕.biUnion id
    have hZ₀ : Z₀ ⊆ S := Finset.subset_union_left
    have hfam : ∀ Z ∈ 𝓕, Z ⊆ S ∧ ∀ x ∈ Z, good x := by
      intro Z hZ
      constructor
      · exact (Finset.subset_biUnion_of_mem id hZ).trans Finset.subset_union_right
      · exact hgood Z (h𝓕 hZ)
    exact EndSaving.RadonNikodym.finite_good_family_card S Z₀ N good 𝓕 R M
      hZ₀ (fun x _ => hself x) hsymm (fun x _ => hN x) hfam
      (fun Z₁ _ hg hs => hcount Z₁ hg hs)
  have hfinite : family.Finite := by
    by_contra hn
    have hinf : family.Infinite := not_finite.mp hn
    obtain ⟨𝓕, h𝓕, hcard⟩ := hinf.exists_subset_card_eq (B + 1)
    have hbound := hfiniteBound 𝓕 h𝓕
    omega
  constructor
  · exact hfinite
  · have hb := hfiniteBound hfinite.toFinset (by simp [family])
    simpa only [Set.ncard_eq_toFinset_card family hfinite, family, B] using hb

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Counting
