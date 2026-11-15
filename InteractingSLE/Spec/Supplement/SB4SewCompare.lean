/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewTransport

/-!
# The closed-side comparison needed for sewing at real contacts

The crossing certificate used in SB3 applies also when the forbidden point is
real. Applying that same certificate before restricting to the physical
half-plane gives closed Jordan-side containment. Reflection and the actual-tail
transport then give the physical sewn comparison.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B

namespace InteractingSLE.Theorem14.SB

/-- SB3's finite crossing certificate gives the closed Jordan-side conclusion,
including real available endpoints. It uses the same finite S1 comparisons. -/
theorem available_subset_closedLeftSide_of_prefix_comparisons
    {γ η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {u : ℝ}
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) (hu : u ≤ 0) (hη0 : η 0 = u)
    (hS1 : ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ →
      IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) η a) :
    η '' {t | (t : ℝ≥0∞) ≤ ζ} ⊆ closedLeftSide γ := by
  rintro _ ⟨t, ht, rfl⟩
  by_cases hzS : η t ∈ seedRayClosure γ
  · exact Or.inr hzS
  have h0 : (γ 0).im = 0 := by rw [hγ0]; rfl
  have hs : η t ∈ leftSide γ ∪ rightSide γ :=
    (compl_seedRayClosure_eq hγ h0) ▸ hzS
  rcases hs with hzL | hzR
  · exact Or.inl hzL
  · exfalso
    obtain ⟨η₀, hη₀, -⟩ := hS1 0 t ht
    have P₀ := isProperCurve_of_isProperCompletion hη₀
    have e₀ : η₀ 0 = u := (hη₀.2.2.2.2 0 zero_le).trans hη0
    have hu₀ : (η₀ 0).im = 0 := by rw [e₀]; rfl
    have hu₀' : (η₀ 0).re ≤ 0 := by rw [e₀]; exact hu
    have ht₀ : η₀ t = η t := hη₀.2.2.2.2 t le_rfl
    obtain ⟨t₁, ht₁, hcl⟩ :=
      exists_crossing_certificate hγ hγ0 P₀ hu₀ hu₀' (ht₀ ▸ hzR)
    obtain ⟨s, hs⟩ := eventually_atTop.1
      (hγ.2.2.2.eventually_gt_atTop (‖η₀ t₁‖ + 1))
    obtain ⟨η₁, hη₁, hsub⟩ := hS1 s t ht
    have P₁ := isProperCurve_of_isProperCompletion hη₁
    have hagree : ∀ τ ≤ t, η₁ τ = η₀ τ := fun τ hτ =>
      (hη₁.2.2.2.2 τ hτ).trans (hη₀.2.2.2.2 τ hτ).symm
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1
      (eventually_mem_leftSide_of_eqOn P₀ P₁ hu₀ hagree ht₁)
    obtain ⟨w, ⟨⟨r, rfl⟩, hwL⟩, hwd⟩ :=
      Metric.mem_closure_iff.1 hcl (min ε 1) (lt_min hε one_pos)
    have hw₁ : γ r ∈ leftSide η₁ :=
      hball (by rw [dist_comm]; exact hwd.trans_le (min_le_left _ _)) hwL
    have hrs : r ≤ s := by
      by_contra hrs
      have h1 := hs r (not_le.1 hrs).le
      have h2 : ‖γ r‖ ≤ ‖η₀ t₁‖ + dist (η₀ t₁) (γ r) := by
        have := norm_le_norm_add_norm_sub' (γ r) (η₀ t₁)
        rw [dist_eq_norm, norm_sub_rev]
        linarith only [this]
      have h3 : dist (η₀ t₁) (γ r) < 1 := hwd.trans_le (min_le_right _ _)
      linarith only [h1, h2, h3]
    have hmem : γ r ∈ closedRightSide η₁ :=
      hsub (Or.inl ⟨r, ⟨zero_le, hrs⟩, rfl⟩)
    have hu₁ : (η₁ 0).im = 0 := by rw [hagree 0 zero_le]; exact hu₀
    rcases hmem with hR | hS
    · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide P₁ hu₁) hw₁ hR
    · exact connectedComponentIn_subset _ _ hw₁ hS

/-- Reflection exchanges the closed Jordan sides of a proper curve. -/
theorem refl_mem_closedRightSide_of_mem_closedLeftSide {γ : ℝ≥0 → ℂ}
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0) {z : ℂ}
    (hz : z ∈ closedLeftSide γ) :
    Supp9B.refl z ∈ closedRightSide (reflectCurve γ) := by
  rcases hz with hzL | hzS
  · exact Or.inl (refl_image_leftSide_subset hγ.2.2.1
      (by rw [hγ0]; rfl) ⟨z, hzL, rfl⟩)
  · exact Or.inr (refl_image_seedRayClosure_subset γ ⟨z, hzS, rfl⟩)

/-- A reflected relative SB3 comparison transports to the physical right side.
The input chart is the reflected right-entry chart of SB4. -/
theorem image_available_subset_closedRightSide_of_actual_tail
    {p : ℝ → ℂ} {β γ η : ℝ≥0 → ℂ} {c : Chart} {g : ℂ → ℂ}
    {tL : ℝ≥0} {ζ : ℝ≥0∞} {u : ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hβ : IsProperCurve β) (hβ0 : β 0 = 0)
    (hA : p '' Icc 0 1 ⊆ closedRightSide β)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hentry : β tL = realMin (p '' Icc 0 1))
    (hγ : IsProperCurve γ) (hγ0 : γ 0 = 0)
    (htail : ∀ s, g (γ s) = β (tL + s))
    (hfree : ∃ x : ℝ, 0 < x ∧ realMax (p '' Icc 0 1) < x ∧ (x : ℂ) ∉ range β)
    (hu : u ≤ 0) (hη0 : η 0 = u)
    (hηH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → 0 ≤ (η t).im)
    (hS1 : ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ →
      IsOneSided (reflectCurve γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) η a) :
    g '' (Supp9B.refl '' (η '' {t | (t : ℝ≥0∞) ≤ ζ})) ⊆ closedRightSide β := by
  have hγr := isProperCurve_reflectCurve hγ
  have hγr0 : reflectCurve γ 0 = 0 := by
    simp only [reflectCurve, hγ0, Supp9B.refl, map_zero, neg_zero]
  have hside := available_subset_closedLeftSide_of_prefix_comparisons hγr hγr0 hu hη0 hS1
  apply (image_mono ?_).trans
    (image_closedRightSide_of_actual_tail hp hp0 hpH hβ hβ0 hA hc hgc hgi
      hentry hγ hγ0 htail hfree)
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  have hz := refl_mem_closedRightSide_of_mem_closedLeftSide hγr hγr0
    (hside ⟨t, ht, rfl⟩)
  rw [reflectCurve_reflectCurve] at hz
  exact ⟨hz, by simpa only [mem_ofPred_eq, refl_im] using hηH t ht⟩

end InteractingSLE.Theorem14.SB
