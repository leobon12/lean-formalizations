/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntEnvelopePrefix

/-!
# BeforeExit is equivalent to separation of the raw closures from later tails

For actual retained prefixes the enclosing parameter bounds exist already.
Thus only the geometric selection of a later common exit remains. No
capped-program ArcHistory or connectedness of a raw set is required here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntEnvelope

open WalkIntFill WalkIntActive WalkMean

/-- A subset of an initial segment, including its closure, avoids every
strictly later tail of the same injective proper curve. -/
theorem disjoint_closure_tail_of_cutoff {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α)
    {A : Set ℂ} {a s : ℝ≥0} (hA : A ⊆ α '' Icc 0 a) (has : a < s) :
    Disjoint (closure A) (α '' Ici s) := by
  have he := WalkCont.isClosedEmbedding_of_isProperCurve hα
  have hd : Disjoint (α '' Icc 0 a) (α '' Ici s) :=
    (disjoint_image_iff he.injective).2 (Set.disjoint_left.2 fun t ht hs =>
      (not_le_of_gt has) (hs.trans ht.2))
  exact hd.mono_left (closure_minimal hA (isCompact_Icc.image he.continuous).isClosed)

/-- Geometric separation from later tails constructs BeforeExit. Both
enclosing cutoffs are proved from the actual retained raw sets. -/
theorem exists_beforeExit_of_tail_separation {sR sL : ExplState} (J : RetainedPair sR sL)
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    {C : Set ℂ} {s t : ℝ≥0} (hs : 0 < s) (ht : 0 < t) (hmeet : α s = β t)
    (hsepR : Disjoint (closure J.right.raw) (α '' Ici s))
    (hsepL : Disjoint (closure J.left.raw) (β '' Ici t)) (hC : α s ∈ closure C) :
    ∃ B : BeforeExit J C α β, B.rightExit = s ∧ B.leftExit = t := by
  obtain ⟨a, has, ha⟩ := exists_prefix_cutoff_before J.right hα hR hs hsepR
  obtain ⟨b, hbt, hb⟩ := exists_prefix_cutoff_before J.left hβ hL ht hsepL
  exact ⟨⟨a, b, s, t, subset_closure.trans ha, subset_closure.trans hb,
    has, hbt, hmeet, hC⟩, rfl, rfl⟩

/-- An exact physical reformulation of the old selection input. This
equivalence neither assumes a history nor asserts that the selection exists. -/
theorem beforeExit_iff_tail_separation {sR sL : ExplState} (J : RetainedPair sR sL)
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    {C : Set ℂ} : Nonempty (BeforeExit J C α β) ↔
      ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧ α s = β t ∧
        Disjoint (closure J.right.raw) (α '' Ici s) ∧
        Disjoint (closure J.left.raw) (β '' Ici t) ∧ α s ∈ closure C := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.rightExit, B.leftExit, (zero_le.trans_lt B.right_lt),
      (zero_le.trans_lt B.left_lt), B.meet,
      disjoint_closure_tail_of_cutoff hα B.right_raw B.right_lt,
      disjoint_closure_tail_of_cutoff hβ B.left_raw B.left_lt, B.exit_closure⟩
  · rintro ⟨s, t, hs, ht, hm, hsepR, hsepL, hC⟩
    obtain ⟨B, -, -⟩ := exists_beforeExit_of_tail_separation J hα hβ hR hL
      hs ht hm hsepR hsepL hC
    exact ⟨B⟩

/-- The active-domain conclusion from physical tail separation. The
remaining selection hypothesis contains no parameter cutoffs or histories. -/
theorem active_retainedPair_of_tail_separation {sR sL : ExplState} (J : RetainedPair sR sL)
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range α) (range β))
    (hTail : ∃ s t : ℝ≥0, 0 < s ∧ 0 < t ∧ α s = β t ∧
      Disjoint (closure J.right.raw) (α '' Ici s) ∧
      Disjoint (closure J.left.raw) (β '' Ici t) ∧ α s ∈ closure C) :
    C ⊆ H \ fillH J.raw := by
  obtain ⟨B⟩ := (beforeExit_iff_tail_separation J hα hβ hR hL).2 hTail
  exact active_retainedPair_of_beforeExit J hα hβ horder hC B

end InteractingSLE.Theorem14.WalkIntEnvelope
