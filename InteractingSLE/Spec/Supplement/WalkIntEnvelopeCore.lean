/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntChronoRetained

/-!
# Least initial segments enclosing bounded subsets of a proper walk

The raw retained sets need not be connected. Properness alone bounds all
their parameters. The last parameter belongs to the physical closure,
unless the enclosing segment consists only of the seed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntEnvelope

/-- A bounded subset of a proper curve has a least enclosing initial
segment. Its endpoint is in the subset's closure, except at parameter zero. -/
theorem exists_least_cutoff {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α)
    {A : Set ℂ} (hb : Bornology.IsBounded A) (hA : A ⊆ range α) :
    ∃ a : ℝ≥0, closure A ⊆ α '' Icc 0 a ∧ (a = 0 ∨ α a ∈ closure A) ∧
      ∀ b : ℝ≥0, A ⊆ α '' Icc 0 b → a ≤ b := by
  have he := WalkCont.isClosedEmbedding_of_isProperCurve hα
  have hcl : closure A ⊆ range α := closure_minimal hA he.isClosed_range
  have hc := he.isCompact_preimage
    (hb.isCompact_closure.union (isCompact_singleton : IsCompact {α 0}))
  obtain ⟨a, ha, hmax⟩ := hc.exists_isGreatest ⟨0, Or.inr (mem_singleton _)⟩
  have hend : a = 0 ∨ α a ∈ closure A := by
    rcases ha with ha | ha
    · exact Or.inr ha
    · exact Or.inl (he.injective (mem_singleton_iff.1 ha))
  refine ⟨a, ?_, hend, ?_⟩
  · intro z hz
    obtain ⟨t, rfl⟩ := hcl hz
    exact ⟨t, ⟨zero_le, hmax (Or.inl hz)⟩, rfl⟩
  · intro b hAb
    rcases hend with rfl | ha
    · exact zero_le
    · have hclosed : IsClosed (α '' Icc 0 b) :=
        (isCompact_Icc.image he.continuous).isClosed
      obtain ⟨t, ht, heq⟩ := closure_minimal hAb hclosed ha
      exact he.injective heq ▸ ht.2

/-- Avoiding the closed proper tail makes an enclosing cutoff strictly
earlier than the given positive exit, with no chronological history input. -/
theorem exists_cutoff_before_of_disjoint_tail {α : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) {A : Set ℂ} (hb : Bornology.IsBounded A)
    (hA : A ⊆ range α) {s : ℝ≥0} (hs : 0 < s)
    (hsep : Disjoint (closure A) (α '' Ici s)) :
    ∃ a : ℝ≥0, a < s ∧ closure A ⊆ α '' Icc 0 a := by
  obtain ⟨a, ha, hend, -⟩ := exists_least_cutoff hα hb hA
  refine ⟨a, ?_, ha⟩
  rcases hend with rfl | hend
  · exact hs
  · exact lt_of_not_ge fun hsa => Set.disjoint_left.1 hsep hend ⟨a, hsa, rfl⟩

end InteractingSLE.Theorem14.WalkIntEnvelope
