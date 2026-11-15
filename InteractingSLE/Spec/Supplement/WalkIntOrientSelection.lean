/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntOrientCountable

/-!
# Selection in the bounded admissible completed-prefix pool

Directedness and countable cofinality construct the reference sequence.
The one remaining pointwise physical input is written out as hClosedPoint;
no sequence or compatibility with finite-word witnesses is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntOrient

open WalkBdry WalkIntClosed

/-- Construct a nested completed-prefix family cofinal in all admissible
completed pairs. The physical pointwise selection is still the exact
named hypothesis hClosedPoint, not a proved assertion about actual runs. -/
theorem exists_admissible_closed_family {c : Chart} {sR sL : ExplState}
    {α β : ℝ≥0 → ℂ}
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    (hClosedPoint : ∀ x : ℝ, ∃ J : ClosedPair sR sL, ∃ ρ : ℝ, 0 < ρ ∧
      (wsetOf sR ∪ wsetOf sL) ∩ ball (GW4Traverse.invExt c (x : ℂ)) ρ ⊆ J.raw ∧
      (Bornology.IsBounded (c.dom : Set ℂ) → ∃ s t : ℝ≥0,
        0 < s ∧ 0 < t ∧ α s = β t ∧
          Disjoint (closure J.right.raw) (α '' Ici s) ∧
          Disjoint (closure J.left.raw) (β '' Ici t) ∧ α s ∈ closure (c.dom : Set ℂ))) :
    ∃ pair : ℕ → ClosedPair sR sL, Monotone (fun i => (pair i).raw) ∧
      (Bornology.IsBounded (c.dom : Set ℂ) → ∀ i, ∃ s t : ℝ≥0,
        0 < s ∧ 0 < t ∧ α s = β t ∧
          Disjoint (closure (pair i).right.raw) (α '' Ici s) ∧
          Disjoint (closure (pair i).left.raw) (β '' Ici t) ∧
          α s ∈ closure (c.dom : Set ℂ)) ∧
      (∀ x : ℝ, ∃ i : ℕ, ∃ ρ : ℝ, 0 < ρ ∧
        (wsetOf sR ∪ wsetOf sL) ∩
          ball (GW4Traverse.invExt c (x : ℂ)) ρ ⊆ (pair i).raw) ∧
      ∀ J : ClosedPair sR sL,
        (Bornology.IsBounded (c.dom : Set ℂ) → ∃ s t : ℝ≥0,
          0 < s ∧ 0 < t ∧ α s = β t ∧
            Disjoint (closure J.right.raw) (α '' Ici s) ∧
            Disjoint (closure J.left.raw) (β '' Ici t) ∧ α s ∈ closure (c.dom : Set ℂ)) →
        ∃ i, J.raw ⊆ (pair i).raw := by
  let I := {J : ClosedPair sR sL // Bornology.IsBounded (c.dom : Set ℂ) →
    ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧ α s = β t ∧
      Disjoint (closure J.right.raw) (α '' Ici s) ∧
      Disjoint (closure J.left.raw) (β '' Ici t) ∧ α s ∈ closure (c.dom : Set ℂ)}
  have hdir : Directed (· ⊆ ·) (fun J : I => J.val.raw) := by
    intro J K
    obtain ⟨M, hJM, hKM, hM⟩ := exists_admissible_closed_upper
      J.val K.val horder J.property K.property
    exact ⟨⟨M, hM⟩, hJM, hKM⟩
  have hLocal : ∀ x : ℝ, ∃ J : I, ∃ ρ : ℝ, 0 < ρ ∧
      (wsetOf sR ∪ wsetOf sL) ∩ ball (GW4Traverse.invExt c (x : ℂ)) ρ ⊆ J.val.raw := by
    intro x
    obtain ⟨J, ρ, hρ, hloc, htail⟩ := hClosedPoint x
    exact ⟨⟨J, htail⟩, ρ, hρ, hloc⟩
  obtain ⟨J₀, _⟩ := hLocal 0
  let : Nonempty I := ⟨J₀⟩
  obtain ⟨a, hmono, hdom⟩ := exists_monotone_closed_raw_cofinal (fun J : I => J.val) hdir
  refine ⟨fun i => (a i).val, hmono, fun hb i => (a i).property hb, ?_,
    fun J hJ => hdom ⟨J, hJ⟩⟩
  intro x
  obtain ⟨J, ρ, hρ, hloc⟩ := hLocal x
  obtain ⟨i, hi⟩ := hdom J
  exact ⟨i, ρ, hρ, hloc.trans hi⟩

end InteractingSLE.Theorem14.WalkIntOrient
