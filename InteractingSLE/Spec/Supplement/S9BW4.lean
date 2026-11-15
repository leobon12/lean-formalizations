/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.S9BExtend
import InteractingSLE.Spec.Supplement.S9Propagation

/-!
# Supplement §9, Lemma W4 (extension without a new mutual contact), pathwise

Packet PROVE-SUPP9-C. `extendsWithoutNewContact_of_slits` proves the pathwise W4 property
`Supp9.ExtendsWithoutNewContact` (PROVE-SUPP9) for two curves from real seeds `β(0) ≤ α(0)` all of whose finite
available prefixes have slit completions (proper completions whose new points lie in `ℍ` off the prefix: the
Loewner slits), from one deterministic planar input, `W4TipAccessStatement`:

> at an extension of the first path without a new contact, one of the two tips lies in the closure of the joint
> domain (and the second tip, when it is the one, is not an old contact).

This is the trapping classification of Lemma G13's proof (supplement p. 506: "Suppose first that `b` lies in the
closure of a bounded component `C` of `ℍ \ a` … The case in which `a` is trapped by `b` is identical. **Neither branch
is trapped.** …"), applied after the last old common point as in W4's proof (p. 532: "the original finite suffixes lie
in `closure(D_q)`"); it is **not proved in Lean** here. Everything else in W4 is: the first path is extended by
`hasOrderedProperCompletions_extend_left` (S9BExtend), the second by reflection
(`hasOrderedProperCompletions_extend_right`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Supp9B

/-- A **slit completion** of `γ([0, b])`: a proper completion whose points after `b` lie in `ℍ` and off `γ([0, b])`.
For a Loewner trace this is the inverse image of a vertical ray in the chart at time `b`. -/
def IsSlitCompletion (γ : ℝ≥0 → ℂ) (b : ℝ≥0) (S : ℝ≥0 → ℂ) : Prop :=
  IsProperCompletion γ b S ∧ ∀ t, b < t → 0 < (S t).im ∧ S t ∉ γ '' Icc 0 b

/-- **Named input (deterministic planar topology; Lemma G13's trapping classification after the last common point,
used in W4's proof, supplement pp. 506, 532).** Let `𝓔(α([0, a]), β([0, c]))` hold for curves from real seeds
`β(0) ≤ α(0)`, let `α([0, a'])` (`a < a'`) and `β([0, c])` have slit completions, and let `α([a, a'])` avoid
`β([0, c])`. Then the tip `α(a')` lies in the closure of the joint domain, or the tip `β(c)` does and is not a point
of `α([0, a])`. **Not proved in Lean.** -/
def W4TipAccessStatement : Prop :=
  ∀ (α β S Sβ : ℝ≥0 → ℂ) (a a' c : ℝ≥0), HasOrderedProperCompletions α a β c → (α 0).im = 0 →
    (β 0).im = 0 → (β 0).re ≤ (α 0).re → a < a' → IsSlitCompletion α a' S → IsSlitCompletion β c Sβ →
    (∀ x ∈ Icc a a', ∀ y ∈ Icc 0 c, α x ≠ β y) →
    α a' ∈ closure (jointDomain α a' β c) ∨
      (β c ∈ closure (jointDomain α a' β c) ∧ ∀ x ≤ a, β c ≠ α x)

theorem isSlitCompletion_reflectCurve {γ S : ℝ≥0 → ℂ} {b : ℝ≥0} (h : IsSlitCompletion γ b S) :
    IsSlitCompletion (reflectCurve γ) b (reflectCurve S) := by
  refine ⟨isProperCompletion_reflectCurve h.1, fun t ht => ⟨by simpa [reflectCurve] using (h.2 t ht).1, ?_⟩⟩
  rintro ⟨x, hx, hxt⟩
  exact (h.2 t ht).2 ⟨x, hx, refl_injective hxt⟩

theorem IsSlitCompletion.mono {γ S : ℝ≥0 → ℂ} {b b' : ℝ≥0} (h : IsSlitCompletion γ b S) (hb : b' ≤ b) :
    IsProperCompletion γ b' S :=
  ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, fun t ht => h.1.2.2.2.2 t (ht.trans hb)⟩

section Extend

variable {α β : ℝ≥0 → ℂ} {a a' c c' : ℝ≥0}

/-- **Lemma W4 for the first path**, from the tip-access input. -/
theorem hasOrderedProperCompletions_extend_left_of_access (hND : W4TipAccessStatement)
    (h : HasOrderedProperCompletions α a β c) (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0)
    (hseed : (β 0).re ≤ (α 0).re) (haa' : a < a') {S Sβ : ℝ≥0 → ℂ} (hS : IsSlitCompletion α a' S)
    (hSβ : IsSlitCompletion β c Sβ) (hnew : ∀ x ∈ Icc a a', ∀ y ∈ Icc 0 c, α x ≠ β y) :
    HasOrderedProperCompletions α a' β c :=
  hasOrderedProperCompletions_extend_left h h0 hβ0 hseed haa' hS.1 hS.2 hnew
    (hND α β S Sβ a a' c h h0 hβ0 hseed haa' hS hSβ hnew)

/-- **Lemma W4 for the second path**, by reflection. -/
theorem hasOrderedProperCompletions_extend_right_of_access (hND : W4TipAccessStatement)
    (h : HasOrderedProperCompletions α a β c) (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0)
    (hseed : (β 0).re ≤ (α 0).re) (hcc' : c < c') {Sα Sβ : ℝ≥0 → ℂ} (hSα : IsSlitCompletion α a Sα)
    (hSβ : IsSlitCompletion β c' Sβ) (hnew : ∀ y ∈ Icc c c', ∀ x ∈ Icc 0 a, β y ≠ α x) :
    HasOrderedProperCompletions α a β c' := by
  have hr := hasOrderedProperCompletions_reflect h h0 hβ0 hseed
  have hr0 : (reflectCurve β 0).im = 0 := by simp [reflectCurve, hβ0]
  have hr0' : (reflectCurve α 0).im = 0 := by simp [reflectCurve, h0]
  have hrseed : (reflectCurve α 0).re ≤ (reflectCurve β 0).re := by simp [reflectCurve, hseed]
  have hr' := hasOrderedProperCompletions_extend_left_of_access hND hr hr0 hr0' hrseed hcc'
    (isSlitCompletion_reflectCurve hSβ) (isSlitCompletion_reflectCurve hSα)
    fun y hy x hx h' => hnew y hy x hx (refl_injective h')
  have := hasOrderedProperCompletions_reflect hr' hr0 hr0' hrseed
  simpa using this

end Extend

/-- **Lemma W4, pathwise** (supplement p. 532), from the tip-access input: two curves from real seeds
`β(0) ≤ α(0)` whose available prefixes all have slit completions satisfy `ExtendsWithoutNewContact`. -/
theorem extendsWithoutNewContact_of_slits (hND : W4TipAccessStatement) {α β : ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : ℝ≥0∞} (h0 : (α 0).im = 0) (hβ0 : (β 0).im = 0) (hseed : (β 0).re ≤ (α 0).re)
    (hslα : ∀ a : ℝ≥0, (a : ℝ≥0∞) < ζ₁ → ∃ S, IsSlitCompletion α a S)
    (hslβ : ∀ c : ℝ≥0, (c : ℝ≥0∞) < ζ₂ → ∃ S, IsSlitCompletion β c S) :
    Supp9.ExtendsWithoutNewContact α ζ₁ β ζ₂ := by
  intro a a' c c' haa' ha'ζ hcc' hc'ζ hE hcont hα hβ
  have haζ : (a : ℝ≥0∞) < ζ₁ := lt_of_le_of_lt (by exact_mod_cast haa') ha'ζ
  have hcζ : (c : ℝ≥0∞) < ζ₂ := lt_of_le_of_lt (by exact_mod_cast hcc') hc'ζ
  -- extend the first path
  have h1 : HasOrderedProperCompletions α a' β c := by
    rcases haa'.lt_or_eq with hlt | heq
    · obtain ⟨S, hS⟩ := hslα a' ha'ζ
      obtain ⟨Sβ, hSβ⟩ := hslβ c hcζ
      refine hasOrderedProperCompletions_extend_left_of_access hND hE h0 hβ0 hseed hlt hS hSβ ?_
      intro x hx y hy hxy
      have hxa := (hcont x ⟨zero_le, hx.2⟩ y ⟨zero_le, hy.2.trans hcc'⟩ hxy).1
      have hxa' : x = a := le_antisymm hxa hx.1
      exact hα hlt ⟨y, hy, by rw [← hxa']; exact hxy.symm⟩
    · rw [← heq]; exact hE
  -- extend the second path
  rcases hcc'.lt_or_eq with hlt | heq
  · obtain ⟨Sα, hSα⟩ := hslα a' ha'ζ
    obtain ⟨Sβ, hSβ⟩ := hslβ c' hc'ζ
    refine hasOrderedProperCompletions_extend_right_of_access hND h1 h0 hβ0 hseed hlt hSα hSβ ?_
    intro y hy x hx hyx
    have hc := hcont x ⟨zero_le, hx.2⟩ y ⟨zero_le, hy.2⟩ hyx.symm
    have hyc : y = c := le_antisymm hc.2 hy.1
    exact hβ hlt ⟨x, ⟨zero_le, hc.1⟩, by rw [← hyc]; exact hyx.symm⟩
  · rw [← heq]; exact h1

end Supp9B

end InteractingSLE
