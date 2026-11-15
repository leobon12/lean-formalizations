/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBoundCutClosing

/-!
# Choosing the two actual raw cutoffs before the closing contact

The geometric closing contact and actual raw cutoff models are proved
separately. Their combination constructs the full hSelect conclusion,
with no selection, collar or tail-separation hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntBoundCut

open WalkBdry WalkIntOrient WalkIntClosed

/-- An injective walk admits a cutoff strictly after a landing and
strictly before an exit known to follow that landing. -/
theorem exists_cutoff_between_landing_exit {α : ℝ≥0 → ℂ} (hinj : Function.Injective α)
    {p : ℂ} {s : ℝ≥0} (hs : 0 < s) (hbefore : ∀ u, α u = p → u < s) :
    ∃ a : ℝ≥0, a < s ∧ ∀ u, α u = p → u < a := by
  by_cases hp : p ∈ range α
  · obtain ⟨u, hu⟩ := hp
    obtain ⟨a, hua, has⟩ := exists_between (hbefore u hu)
    exact ⟨a, has, fun v hv => hinj (hv.trans hu.symm) ▸ hua⟩
  · exact ⟨0, hs, fun u hu => False.elim (hp ⟨u, hu⟩)⟩

/-- Actual raw models at arbitrary full-walk parameters and the existing
component geometry construct hSelect, including the bounded case. -/
theorem initial_selection_of_component_chart {sR sL : ExplState} {α β : ℝ≥0 → ℂ}
    (hα : Supp9B.IsProperCurve α) (hβ : Supp9B.IsProperCurve β)
    (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (horder : ∀ s s' t t' : ℝ≥0, α s = β t → α s' = β t' → (s < s' ↔ t < t'))
    (hno : ∀ a b : ℝ≥0, a < b → ¬ α '' Icc a b ⊆ range β)
    {c : Chart} (hC : (c.dom : Set ℂ) ∈ betweenComponents (range α) (range β))
    (hc : IsComponentChart (range α) (range β) (c.dom : Set ℂ) c)
    (hRawR : ∀ a : ℝ≥0, ∃ R : ClosedPrefix sR, R.raw = (α '' Icc 0 a) ∩ H)
    (hRawL : ∀ b : ℝ≥0, ∃ L : ClosedPrefix sL, L.raw = (β '' Icc 0 b) ∩ H) :
    ∀ x : ℝ, ∃ (J : ClosedPair sR sL) (a b : ℝ≥0),
      J.right.raw = (α '' Icc 0 a) ∩ H ∧ J.left.raw = (β '' Icc 0 b) ∩ H ∧
      (∀ u, α u = GW4Traverse.invExt c (x : ℂ) → u < a) ∧
      (∀ v, β v = GW4Traverse.invExt c (x : ℂ) → v < b) ∧
      (Bornology.IsBounded (c.dom : Set ℂ) → ∃ s t : ℝ≥0,
        a < s ∧ b < t ∧ α s = β t ∧ α s ∈ closure (c.dom : Set ℂ)) := by
  have hTimes : ∀ x : ℝ, ∃ a b : ℝ≥0,
      (∀ u, α u = GW4Traverse.invExt c (x : ℂ) → u < a) ∧
      (∀ v, β v = GW4Traverse.invExt c (x : ℂ) → v < b) ∧
      (Bornology.IsBounded (c.dom : Set ℂ) → ∃ s t : ℝ≥0,
        a < s ∧ b < t ∧ α s = β t ∧ α s ∈ closure (c.dom : Set ℂ)) := by
    by_cases hb : Bornology.IsBounded (c.dom : Set ℂ)
    · obtain ⟨s, t, hs, ht, hmeet, hcl, hbefore⟩ := exists_closing_contact
        (GW4Leaf.isCompleteSimpleFlow_of_isProperCurve hα hα0)
        (GW4Leaf.isCompleteSimpleFlow_of_isProperCurve hβ hβ0) horder hno hC hc hb
      intro x
      obtain ⟨a, has, ha⟩ := exists_cutoff_between_landing_exit hα.2.1 hs (hbefore x).1
      obtain ⟨b, hbt, hb⟩ := exists_cutoff_between_landing_exit hβ.2.1 ht (hbefore x).2
      exact ⟨a, b, ha, hb, fun _ => ⟨s, t, has, hbt, hmeet, hcl⟩⟩
    · intro x
      refine ⟨curveTime α (GW4Traverse.invExt c (x : ℂ)) + 1,
        curveTime β (GW4Traverse.invExt c (x : ℂ)) + 1, ?_, ?_, fun h => (hb h).elim⟩
      · intro u hu
        rw [← hu, curveTime_apply hα.2.1]
        exact lt_add_one u
      · intro v hv
        rw [← hv, curveTime_apply hβ.2.1]
        exact lt_add_one v
  intro x
  obtain ⟨a, b, ha, hb, hexit⟩ := hTimes x
  obtain ⟨R, hR⟩ := hRawR a
  obtain ⟨L, hL⟩ := hRawL b
  obtain ⟨J, hJR, hJL⟩ := exists_closedPair R L
  exact ⟨J, a, b, hJR ▸ hR, hJL ▸ hL, ha, hb, hexit⟩

end InteractingSLE.Theorem14.WalkIntBoundCut
