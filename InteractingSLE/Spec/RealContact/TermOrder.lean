/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermPathClock
import InteractingSLE.Spec.Supplement.RLCGlue

/-!
# Real points of the left path do not pass the right seed (contact order)

Packet PROVE-RC-TERM, second run (ruling R124). Deterministic consequences of the ordered proper completions (W0)
and the contact-order theorem (`Supp9B.contact_order`, Lemma G5 / Aux. lemma 84):

* `mem_range_of_mem_closedLeftSide`, `mem_range_of_mem_closedRightSide`: a real point strictly on the far side of the
  seed which lies in a closed side of a proper curve is on the curve;
* **`real_le_seed_of_order`**: let `η₁` (from `x₁`) and `η₂` (from `x₂ ≤ x₁`) have ordered proper completions at
  `(s, t₀)`, let `η₁ s = y` be real with `y < x₂`, off `η₂([0, t₀])`, and let `η₂ t₀ = q` be real, off `η₁([0, s])`.
  Then `q ≤ x₁`. (Otherwise `q` lies on the completion of `η₁` after `s` and `y` on the completion of `η₂` after
  `t₀`: two contacts in reversed order.)

So on the trigger event of the path statement the completed second path has no real point right of the first seed:
the entry-data hypothesis `IsEntryData.real` of the builder.

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE.RealContact

namespace Term

open Supp9B

/-- A real point right of the seed in the closed left side of a proper curve is on the curve. -/
theorem mem_range_of_mem_closedLeftSide {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) {r : ℝ}
    (hr : (γ 0).re < r) (hm : (r : ℂ) ∈ closedLeftSide γ) : (r : ℂ) ∈ range γ := by
  by_contra hn
  have hS : (r : ℂ) ∉ seedRayClosure γ := by
    rintro (h | ⟨hre, -⟩)
    · exact hn h
    · rw [ofReal_re] at hre
      exact hr.ne' hre
  have hR := RLC.ofReal_mem_rightSide hγ.2.2.1 h0 hr hS
  rw [closedLeftSide_eq] at hm
  rcases hm with hL | hS'
  · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ h0) hL hR
  · exact hS hS'

/-- A real point left of the seed in the closed right side of a proper curve is on the curve. -/
theorem mem_range_of_mem_closedRightSide {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ) (h0 : (γ 0).im = 0) {r : ℝ}
    (hr : r < (γ 0).re) (hm : (r : ℂ) ∈ closedRightSide γ) : (r : ℂ) ∈ range γ := by
  by_contra hn
  have hS : (r : ℂ) ∉ seedRayClosure γ := by
    rintro (h | ⟨hre, -⟩)
    · exact hn h
    · rw [ofReal_re] at hre
      exact hr.ne hre
  have hL := ofReal_mem_leftSide hγ.2.2.1 h0 hr hS
  rcases hm with hR | hS'
  · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ h0) hL hR
  · exact hS hS'

/-- **Real points of the left path do not pass the right seed** (see the module docstring). -/
theorem real_le_seed_of_order {η₁ η₂ : ℝ≥0 → ℂ} {x₁ x₂ : ℝ} (hx : x₂ ≤ x₁) (h₁0 : η₁ 0 = x₁) (h₂0 : η₂ 0 = x₂)
    {s t₀ : ℝ≥0} (hW : HasOrderedProperCompletions η₁ s η₂ t₀) {y : ℝ} (hy : η₁ s = y) (hyx : y < x₂)
    (hc₁ : ∀ u ≤ s, η₁ u ≠ η₂ t₀) (hc₂ : ∀ t ≤ t₀, η₂ t ≠ η₁ s) {q : ℝ} (hq : η₂ t₀ = q) : q ≤ x₁ := by
  by_contra hlt
  have hlt : x₁ < q := not_le.1 hlt
  obtain ⟨α', β', hα', hβ', hord⟩ := hW
  have P₁ := isProperCurve_of_isProperCompletion hα'
  have P₂ := isProperCurve_of_isProperCompletion hβ'
  have hα0 : α' 0 = x₁ := by rw [hα'.2.2.2.2 0 zero_le, h₁0]
  have hβ0 : β' 0 = x₂ := by rw [hβ'.2.2.2.2 0 zero_le, h₂0]
  have h10 : (α' 0).im = 0 := by rw [hα0, ofReal_im]
  have h20 : (β' 0).im = 0 := by rw [hβ0, ofReal_im]
  have hseed : (β' 0).re ≤ (α' 0).re := by rw [hα0, hβ0, ofReal_re, ofReal_re]; exact hx
  -- `q` is on the first completion after `s`
  have hqβ : (q : ℂ) ∈ range β' := ⟨t₀, by rw [hβ'.2.2.2.2 t₀ le_rfl, hq]⟩
  obtain ⟨σ, hσ⟩ := mem_range_of_mem_closedLeftSide P₁ h10 (by rw [hα0, ofReal_re]; exact hlt) (hord hqβ)
  have hsσ : s < σ := by
    by_contra hle
    have hle : σ ≤ s := not_lt.1 hle
    exact hc₁ σ hle (by rw [← hα'.2.2.2.2 σ hle, hσ, hq])
  -- `y` is on the second completion after `t₀`
  have hordR := range_subset_closedRightSide P₁ P₂ h10 h20 hseed hord
  have hyα : (y : ℂ) ∈ range α' := ⟨s, by rw [hα'.2.2.2.2 s le_rfl, hy]⟩
  obtain ⟨τ, hτ⟩ := mem_range_of_mem_closedRightSide P₂ h20 (by rw [hβ0, ofReal_re]; exact hyx) (hordR hyα)
  have htτ : t₀ < τ := by
    by_contra hle
    have hle : τ ≤ t₀ := not_lt.1 hle
    exact hc₂ τ hle (by rw [← hβ'.2.2.2.2 τ hle, hτ, hy])
  have hst : α' s = β' τ := by rw [hα'.2.2.2.2 s le_rfl, hy, hτ]
  have hst' : α' σ = β' t₀ := by rw [hσ, hβ'.2.2.2.2 t₀ le_rfl, hq]
  exact absurd (contact_order P₁ P₂ h10 h20 hseed hord hst hst' hsσ) (not_lt.2 htτ.le)

end Term

end InteractingSLE.RealContact
