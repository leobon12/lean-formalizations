/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntActiveOrder

/-!
# Active containment for actual retained prefix pairs

Every unbounded between component is active for every retained pair.
For a bounded component, the remaining selection data identify the two
recorded prefixes before a common exit contact. Contact order then proves
active containment; it is not a field of the selection data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntActive

open WalkBdry WalkMean WalkIntFill

theorem raw_subset_physical {sR sL : ExplState} (J : RetainedPair sR sL)
    (wR wL : ExplSpec) : J.raw ⊆ physOf wR sR ∪ physOf wL sL := by
  intro z hz
  rcases J.raw_subset hz with hz | hz
  · exact Or.inl (((Set.ext_iff.1 (WalkIntFiber.physOf_inter_H wR sR) z).2 hz).1)
  · exact Or.inr (((Set.ext_iff.1 (WalkIntFiber.physOf_inter_H wL sL) z).2 hz).1)

theorem raw_isBounded {sR sL : ExplState} (J : RetainedPair sR sL) :
    Bornology.IsBounded J.raw := by
  apply J.model.isHull.2.1.subset
  intro z hz
  rw [J.filled]
  have hzH : z ∈ H := (union_subset J.right.raw_subset_H J.left.raw_subset_H) hz
  exact mem_fillH_of_mem_closure hzH (subset_closure hz)

/-- The unbounded component case needs no selected exit or additional
access hypothesis, for any actual pair of retained walk prefixes. -/
theorem active_retainedPair_of_unbounded {sR sL : ExplState} (J : RetainedPair sR sL)
    {wR wL : ExplSpec} {C : Set ℂ}
    (hC : C ∈ betweenComponents (physOf wR sR) (physOf wL sL)) (hCo : IsOpen C)
    (hCu : ¬ Bornology.IsBounded C) : C ⊆ H \ fillH J.raw := by
  obtain ⟨z, -, -, -, hCeq⟩ := hC
  have hCp : IsPreconnected C := by
    rw [hCeq]
    exact isPreconnected_connectedComponentIn
  have hCsub : C ⊆ H \ (physOf wR sR ∪ physOf wL sL) := by
    rw [hCeq]
    exact connectedComponentIn_subset _ _
  have hdis : Disjoint C J.raw := Set.disjoint_left.2 fun p hp hr =>
    (hCsub hp).2 (raw_subset_physical J wR wL hr)
  have hdisCl := hdis.closure_right hCo
  exact subset_H_diff_fillH_of_isPreconnected (raw_isBounded J) hCp
    (fun p hp => ⟨(hCsub hp).1, fun hr => Set.disjoint_left.1 hdisCl hp hr⟩) hCu

/-- Exact remaining prefix/exit selection data for a bounded component.
These are physical parameter inclusions and a later common boundary point;
there is no active-containment or reflected-chart premise. -/
structure BeforeExit {sR sL : ExplState} (J : RetainedPair sR sL)
    (C : Set ℂ) (α β : ℝ≥0 → ℂ) where
  rightTime : ℝ≥0
  leftTime : ℝ≥0
  rightExit : ℝ≥0
  leftExit : ℝ≥0
  right_raw : J.right.raw ⊆ α '' Icc 0 rightTime
  left_raw : J.left.raw ⊆ β '' Icc 0 leftTime
  right_lt : rightTime < rightExit
  left_lt : leftTime < leftExit
  meet : α rightExit = β leftExit
  exit_closure : α rightExit ∈ closure C

/-- Contact order discharges active containment from the named physical
selection data for the actual two retained prefixes. -/
theorem active_retainedPair_of_beforeExit {sR sL : ExplState} (J : RetainedPair sR sL)
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (horder : ∀ u u' v v' : ℝ≥0, α u = β v → α u' = β v' → (u < u' ↔ v < v'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range α) (range β))
    (B : BeforeExit J C α β) : C ⊆ H \ fillH J.raw :=
  active_of_later_common_contact hα hβ horder hC (union_subset_union B.right_raw B.left_raw)
    B.right_lt B.left_lt B.meet B.exit_closure

end InteractingSLE.Theorem14.WalkIntActive
