/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntChronoCap

/-!
# Constructing BeforeExit from physical finite histories

The two proper-curve cutoff parameters are conclusions. It suffices to
give chronological prefix histories and a common component-boundary point
omitted by their physical carriers. Nested carriers also give raw nesting.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntChrono

open WalkIntFill WalkIntActive

/-- Physical history certificates and an omitted common boundary point
construct the old parameter-based input, preserving the chosen exit times. -/
theorem exists_beforeExit_of_histories {sR sL : ExplState} (J : RetainedPair sR sL)
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (P : PrefixHistory J.right α) (Q : PrefixHistory J.left β) {C : Set ℂ}
    {s t : ℝ≥0} (hmeet : α s = β t) (hs : α s ∉ P.carrier) (ht : β t ∉ Q.carrier)
    (hC : α s ∈ closure C) :
    ∃ B : BeforeExit J C α β, B.rightExit = s ∧ B.leftExit = t := by
  obtain ⟨a, has, ha⟩ := P.exists_before hα hs
  obtain ⟨b, hbt, hb⟩ := Q.exists_before hβ ht
  exact ⟨⟨a, b, s, t, ha, hb, has, hbt, hmeet, hC⟩, rfl, rfl⟩

/-- The bounded-component active-domain step from physical finite
histories and an omitted common exit. No cutoff parameter is assumed. -/
theorem active_retainedPair_of_histories {sR sL : ExplState} (J : RetainedPair sR sL)
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    (P : PrefixHistory J.right α) (Q : PrefixHistory J.left β) {C : Set ℂ}
    (hC : C ∈ betweenComponents (range α) (range β))
    (hExit : ∃ s t : ℝ≥0, α s = β t ∧ α s ∉ P.carrier ∧ β t ∉ Q.carrier ∧
      α s ∈ closure C) : C ⊆ H \ fillH J.raw := by
  obtain ⟨s, t, hmeet, hs, ht, hcl⟩ := hExit
  obtain ⟨B, -, -⟩ := exists_beforeExit_of_histories J hα hβ P Q hmeet hs ht hcl
  exact active_retainedPair_of_beforeExit J hα hβ horder hC B

/-- Nested physical histories on both sides give the raw-pair nesting
used by the committed common-integer family. -/
theorem raw_pair_subset_of_histories {sR sL : ExplState} (J J' : RetainedPair sR sL)
    {α β : ℝ≥0 → ℂ} (P : PrefixHistory J.right α) (Q : PrefixHistory J.left β)
    (P' : PrefixHistory J'.right α) (Q' : PrefixHistory J'.left β)
    (hP : P.carrier ⊆ P'.carrier) (hQ : Q.carrier ⊆ Q'.carrier) : J.raw ⊆ J'.raw :=
  union_subset_union (raw_subset_of_history_subset P P' hP) (raw_subset_of_history_subset Q Q' hQ)

end InteractingSLE.Theorem14.WalkIntChrono
