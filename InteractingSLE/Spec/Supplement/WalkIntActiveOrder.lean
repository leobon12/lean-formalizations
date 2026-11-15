/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntActiveContact
import InteractingSLE.Spec.Supplement.S9CTip

/-!
# Contact order gives an unretained continuation to the original target

After a common contact later than both retained cutoffs, the right curve
cannot hit either old prefix. The existing free-point theorem applies to
this proper tail in Hbar. Every between component touching that contact
therefore remains in the original-target complement of the retained union.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntActive

/-- The right tail beyond a later common contact misses both old prefixes.
The contact order is the one already supplied by the walk path facts. -/
theorem tail_disjoint_prefixes {α β : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {a b s t : ℝ≥0} (has : a < s) (hbt : b < t) (hmeet : α s = β t) :
    Disjoint (α '' Ici s) (α '' Icc 0 a ∪ β '' Icc 0 b) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨u, hu, rfl⟩ (⟨v, hv, hve⟩ | ⟨v, hv, hve⟩)
  · have hvu := hα.2.1 hve
    exact (not_le.2 (has.trans_le hu)) (hvu ▸ hv.2)
  · have hus : u < s := (horder u s v t hve.symm hmeet).2 (hv.2.trans_lt hbt)
    exact (not_lt.2 hu) hus

/-- A component touching a common contact beyond both cutoffs is active
for every raw set contained in those initial curve segments. This includes
bounded components and real exit contacts. -/
theorem active_of_later_common_contact {α β : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {C Γ : Set ℂ} (hC : C ∈ betweenComponents (range α) (range β))
    {a b s t : ℝ≥0} (hΓ : Γ ⊆ α '' Icc 0 a ∪ β '' Icc 0 b)
    (has : a < s) (hbt : b < t) (hmeet : α s = β t) (hsC : α s ∈ closure C) :
    C ⊆ H \ fillH Γ := by
  let F := α '' Icc 0 a ∪ β '' Icc 0 b
  have hF : IsCompact F :=
    (isCompact_Icc.image hα.1).union (isCompact_Icc.image hβ.1)
  obtain ⟨z, -, -, -, hCeq⟩ := hC
  have hCp : IsPreconnected C := by
    rw [hCeq]
    exact isPreconnected_connectedComponentIn
  have hCsub : C ⊆ H \ (range α ∪ range β) := by
    rw [hCeq]
    exact connectedComponentIn_subset _ _
  have hCF : C ⊆ H \ F := by
    intro p hp
    refine ⟨(hCsub hp).1, fun hf => (hCsub hp).2 ?_⟩
    rcases hf with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩
    · exact Or.inl (mem_range_self v)
    · exact Or.inr (mem_range_self v)
  have htail := tail_disjoint_prefixes hα horder has hbt hmeet
  have hXu : ¬ Bornology.IsBounded (α '' Ici s) := fun hb =>
    Supp9B.not_isBounded_image_Ioi hα.2.2.2 s (hb.subset (image_mono Ioi_subset_Ici_self))
  have hXF : α '' Ici s ⊆ Hbar \ F := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨hα.2.2.1 v, fun h => Set.disjoint_left.1 htail ⟨v, hv, rfl⟩ h⟩
  have hactive := active_of_unbounded_continuation hF hCp hCF
    (isPreconnected_Ici.image _ hα.1.continuousOn) hXu hXF
    (show α s ∈ α '' Ici s from ⟨s, mem_Ici.2 le_rfl, rfl⟩) hsC
  intro p hp
  exact ⟨(hactive hp).1, fun hf => (hactive hp).2 (fillH_mono hΓ hf)⟩

end InteractingSLE.Theorem14.WalkIntActive
