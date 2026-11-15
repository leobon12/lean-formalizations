/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS2LiftSide

/-!
# The real-connector step of SB3's induction

Packet PROVE-T14-SBTAIL2. Specification p. 633: adjoining a rightward real connector or
the initial bridge preserves S1 with the same proper completion. This is a deterministic
step only; it does not identify the conditional flow after erasing a retained prefix.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace InteractingSLE.Theorem14.SB

/-- Every real point on or to the right of a proper curve's real seed is on its closed
right side, including points of the curve and of its closing ray. -/
theorem ofReal_mem_closedRightSide_of_seed_le {γ : ℝ≥0 → ℂ}
    (hγ : Supp9B.IsProperCurve γ) (h0 : (γ 0).im = 0) {x : ℝ}
    (hx : (γ 0).re ≤ x) : (x : ℂ) ∈ Supp9B.closedRightSide γ := by
  by_cases hS : (x : ℂ) ∈ seedRayClosure γ
  · exact Or.inr hS
  · refine Or.inl (ofReal_mem_rightSide_of_gt hγ h0 ?_ hS)
    rcases hx.eq_or_lt with heq | hlt
    · exact False.elim (hS (Or.inr ⟨by simpa only [Complex.ofReal_re] using heq.symm,
        by rw [Complex.ofReal_im, h0]⟩))
    · exact hlt

/-- Adjoining arbitrary original-real points to the right of the upper seed preserves
S1. The existing proper completion is retained, so this also applies at a terminal stop. -/
theorem IsOneSided.union_right_real {A : Set ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0}
    (h : IsOneSided A β a) (h0 : (β 0).im = 0) {T : Set ℝ}
    (hT : ∀ x ∈ T, (β 0).re ≤ x) :
    IsOneSided (A ∪ ((↑) : ℝ → ℂ) '' T) β a := by
  obtain ⟨γ, hγ, hA⟩ := h
  have hγ0 : γ 0 = β 0 := hγ.2.2.2.2 0 zero_le
  have hproper : Supp9B.IsProperCurve γ := ⟨hγ.1, hγ.2.1, hγ.2.2.1, hγ.2.2.2.1⟩
  refine ⟨γ, hγ, union_subset hA ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact ofReal_mem_closedRightSide_of_seed_le hproper (hγ0 ▸ h0)
    (by rw [hγ0]; exact hT x hx)

/-- The next rightward connector in SB3 preserves its induction assertion. -/
theorem IsOneSided.union_connector {A : Set ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0}
    (h : IsOneSided A β a) (h0 : (β 0).im = 0) {q w : ℝ}
    (hq : (β 0).re ≤ q) : IsOneSided (A ∪ ((↑) : ℝ → ℂ) '' Icc q w) β a :=
  h.union_right_real h0 (fun _ hx => hq.trans hx.1)

/-- SB3's separately labelled bridge is retained without changing the completion. -/
theorem IsOneSided.union_bridge {A : Set ℂ} {β : ℝ≥0 → ℂ} {a : ℝ≥0} {u : ℝ}
    (h : IsOneSided A β a) (h0 : β 0 = (u : ℂ)) :
    IsOneSided (A ∪ ((↑) : ℝ → ℂ) '' Icc u 0) β a := by
  apply h.union_connector
  · rw [h0, Complex.ofReal_im]
  · rw [h0, Complex.ofReal_re]

end InteractingSLE.Theorem14.SB
