/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronAE
import InteractingSLE.Spec.Supplement.WalkIntLocalTail
import InteractingSLE.Spec.Supplement.WalkIntOrientLeaf

/-!
# Bounded pointwise collars from chronological cutoff placement

Actual prefix histories and their initial-segment identities are proved
in the preceding modules. The remaining named geometric choice places
those cutoffs after each finite landing and before a common closing
contact. Radii and closed-tail separation are conclusions here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntRunChron

open WalkBdry WalkMean WalkIntClosed

/-- Completed prefixes use the same proper-tail collar theorem as live
prefixes. The finite endpoint is included in their actual raw identity. -/
theorem exists_closed_collar_of_initial_segment {s : ExplState} (R : ClosedPrefix s)
    {α : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) {w : ExplSpec}
    (hRange : range α = physOf w s) {a : ℝ≥0}
    (hraw : R.raw = (α '' Icc 0 a) ∩ H) {p : ℂ}
    (hbefore : ∀ u, α u = p → u < a) :
    ∃ ρ : ℝ, 0 < ρ ∧ wsetOf s ∩ ball p ρ ⊆ R.raw := by
  obtain ⟨ρ, hρ, hdis⟩ := WalkIntLocal.exists_ball_disjoint_tail hα hbefore
  refine ⟨ρ, hρ, ?_⟩
  rintro z ⟨hw, hz⟩
  have hzphys : z ∈ physOf w s :=
    ((Set.ext_iff.1 (WalkIntFiber.physOf_inter_H w s) z).2 hw).1
  obtain ⟨u, rfl⟩ := hRange.symm ▸ hzphys
  have hua : u ≤ a := le_of_not_gt fun hau =>
    Set.disjoint_left.1 hdis hz ⟨u, hau.le, rfl⟩
  rw [hraw]
  exact ⟨⟨u, ⟨zero_le, hua⟩, rfl⟩, hw.2⟩

/-- Exact remaining cutoff-placement hypothesis hSelect. Its raw identities
are available for every actual prefix; their simultaneous placement in a
bounded component is still unproved. No collar or tail condition is input. -/
theorem closed_pointwise_of_initial_selection {c : Chart} {sR sL : ExplState}
    {α β : ℝ≥0 → ℂ} (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    {wR wL : ExplSpec} (hR : range α = physOf wR sR) (hL : range β = physOf wL sL)
    (hSelect : ∀ x : ℝ, ∃ (J : ClosedPair sR sL) (a b : ℝ≥0),
      J.right.raw = (α '' Icc 0 a) ∩ H ∧ J.left.raw = (β '' Icc 0 b) ∩ H ∧
      (∀ u, α u = GW4Traverse.invExt c (x : ℂ) → u < a) ∧
      (∀ v, β v = GW4Traverse.invExt c (x : ℂ) → v < b) ∧
      (Bornology.IsBounded (c.dom : Set ℂ) → ∃ s t : ℝ≥0,
        a < s ∧ b < t ∧ α s = β t ∧ α s ∈ closure (c.dom : Set ℂ))) :
    ∀ x : ℝ, ∃ J : ClosedPair sR sL, ∃ ρ : ℝ, 0 < ρ ∧
      (wsetOf sR ∪ wsetOf sL) ∩ ball (GW4Traverse.invExt c (x : ℂ)) ρ ⊆ J.raw ∧
      (Bornology.IsBounded (c.dom : Set ℂ) → ∃ s t : ℝ≥0,
        0 < s ∧ 0 < t ∧ α s = β t ∧
          Disjoint (closure J.right.raw) (α '' Ici s) ∧
          Disjoint (closure J.left.raw) (β '' Ici t) ∧ α s ∈ closure (c.dom : Set ℂ)) := by
  intro x
  obtain ⟨J, a, b, hrawR, hrawL, hbeforeR, hbeforeL, hExit⟩ := hSelect x
  obtain ⟨ρR, hρR, hlocR⟩ := exists_closed_collar_of_initial_segment J.right hα hR hrawR hbeforeR
  obtain ⟨ρL, hρL, hlocL⟩ := exists_closed_collar_of_initial_segment J.left hβ hL hrawL hbeforeL
  refine ⟨J, min ρR ρL, lt_min hρR hρL, ?_, fun hb => ?_⟩
  · rintro z ⟨hz | hz, hball⟩
    · exact Or.inl (hlocR ⟨hz, ball_subset_ball (min_le_left _ _) hball⟩)
    · exact Or.inr (hlocL ⟨hz, ball_subset_ball (min_le_right _ _) hball⟩)
  · obtain ⟨s, t, has, hbt, hmeet, hcl⟩ := hExit hb
    have hrawR' : J.right.raw ⊆ α '' Icc 0 a := by rw [hrawR]; exact inter_subset_left
    have hrawL' : J.left.raw ⊆ β '' Icc 0 b := by rw [hrawL]; exact inter_subset_left
    exact ⟨s, t, zero_le.trans_lt has, zero_le.trans_lt hbt, hmeet,
      WalkIntEnvelope.disjoint_closure_tail_of_cutoff hα hrawR' has,
      WalkIntEnvelope.disjoint_closure_tail_of_cutoff hβ hrawL' hbt, hcl⟩

end InteractingSLE.Theorem14.WalkIntRunChron
