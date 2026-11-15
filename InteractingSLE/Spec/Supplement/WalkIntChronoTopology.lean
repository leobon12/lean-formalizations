/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntActiveFamily

/-!
# Seeded compact histories are initial segments of a proper curve

Pull the history back by the existing closed embedding of a proper curve.
Compactness supplies its last parameter, while connectedness fills the
interval from the seed. Excluding an exit gives a strict parameter bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal

namespace InteractingSLE.Theorem14.WalkIntChrono

/-- A compact preconnected part of a proper curve containing its seed
is exactly one initial segment, for the given full-curve parametrization. -/
theorem exists_initial_segment {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α)
    {A : Set ℂ} (hAc : IsCompact A) (hAp : IsPreconnected A)
    (hA : A ⊆ range α) (h0 : α 0 ∈ A) : ∃ a : ℝ≥0, A = α '' Icc 0 a := by
  have he := WalkCont.isClosedEmbedding_of_isProperCurve hα
  have hTc : IsCompact (α ⁻¹' A) := he.isCompact_preimage hAc
  have hTp : IsPreconnected (α ⁻¹' A) := by
    rw [← he.isInducing.isPreconnected_image, image_preimage_eq_of_subset hA]
    exact hAp
  obtain ⟨a, ha, hmax⟩ := hTc.exists_isGreatest ⟨0, h0⟩
  have hT : α ⁻¹' A = Icc 0 a :=
    Subset.antisymm (fun t ht => ⟨zero_le, hmax ht⟩) (hTp.Icc_subset h0 ha)
  refine ⟨a, ?_⟩
  rw [← hT, image_preimage_eq_of_subset hA]

/-- A physical exit omitted by the compact seeded history lies strictly
after its last parameter. No separate chronology hypothesis is required. -/
theorem exists_initial_segment_before {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α)
    {A : Set ℂ} (hAc : IsCompact A) (hAp : IsPreconnected A)
    (hA : A ⊆ range α) (h0 : α 0 ∈ A) {s : ℝ≥0} (hs : α s ∉ A) :
    ∃ a : ℝ≥0, a < s ∧ A = α '' Icc 0 a := by
  obtain ⟨a, ha⟩ := exists_initial_segment hα hAc hAp hA h0
  refine ⟨a, lt_of_not_ge (fun hsa => hs ?_), ha⟩
  rw [ha]
  exact ⟨s, ⟨zero_le, hsa⟩, rfl⟩

end InteractingSLE.Theorem14.WalkIntChrono
