/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetTouchWord
import InteractingSLE.Spec.Supplement.RLCCondDetHistWord

/-!
# The outer boundary of a touching retained pair in the retained chart, and its word clauses

Packet PROVE-T15-RET4 (Aux. lemma 85, supplement pp. 299–300, read in the retained chart of Lemma G7, p. 497).
`IsTouchZones α a β b ψ z` is the pathwise content of (OF2) for two prefixes that meet, in a chart inverse `ψ` with the
second tip at `0`: zone data `z` (`GoodT`, junction `J = R₂ = L₁`, second tip `M₂ = 0`, first tip `M₁`) such that

* chart points left of `L₂` (right of `R₁`) are the chart points `T x` of the untouched real points `x` left of the
  second base (right of the first base), which are off both prefixes;
* `(L₂, J)` is mapped into the second prefix, its part `(0, J)` (the right side after the last common point) off the
  first prefix; `(J, M₁)` (the first prefix's left side after the last common point) into the first prefix and off the
  second; `(M₁, R₁)` into the first prefix (its right side — old common points allowed);
* `ψ(L₂)`, `ψ(R₁)` are real points of the second, resp. first, prefix (the extreme real contacts), `ψ(J)` is the last
  common point, `ψ(0)`, `ψ(M₁)` are the tips.

From it the touching zone word has the retained heights (`isRetainedWord_touchWord`, `Supp7.IsRetainedWord`) and the
original datum on the untouched real boundary (`isUntouchedWord_touchWord`, `RLC.IsUntouchedWord`). Old common points
on the outer sides (`ψ w ∈ α ∩ β` for `w < 0` or `w > M₁`) are allowed: `IsRetainedWord` exempts them.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped NNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

namespace RetTouch

open Restart Sec7 Sec7.Lemma76G Sec7.Lemma76G.ZW Supp7

/-- **The outer boundary (OF2) of a touching retained pair in a chart** (Aux. lemma 85 read in the retained chart with
the second tip at `0`). See the module docstring. -/
structure IsTouchZones (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (b : ℝ≥0) (ψ : ℂ → ℂ) (z : ZW) : Prop where
  good : GoodT z
  M₂_eq : z.M₂ = 0
  junction : z.R₂ = z.L₁
  zero_lt_R₂ : 0 < z.R₂
  R₂_lt_M₁ : z.R₂ < z.M₁
  T_spec : ∀ x : ℝ, x < z.a₂ ∨ z.b₁ < x → ψ (z.T x) = x
  notMem_zone : ∀ x : ℝ, x < z.a₂ ∨ z.b₁ < x → ((x : ℝ) : ℂ) ∉ α '' Icc 0 a ∪ β '' Icc 0 b
  zone₀ : ∀ w : ℝ, w < z.L₂ → (ψ w).im = 0 ∧ (ψ w).re < z.a₂ ∧ z.T (ψ w).re = w
  zone₂ : ∀ w : ℝ, z.R₁ < w → (ψ w).im = 0 ∧ z.b₁ < (ψ w).re ∧ z.T (ψ w).re = w
  side₂ : ∀ w : ℝ, z.L₂ < w → w < z.R₂ → ψ w ∈ β '' Icc 0 b
  side₂' : ∀ w : ℝ, 0 < w → w < z.R₂ → ψ w ∉ α '' Icc 0 a
  side₃ : ∀ w : ℝ, z.L₁ < w → w < z.M₁ → ψ w ∈ α '' Icc 0 a ∧ ψ w ∉ β '' Icc 0 b
  side₄ : ∀ w : ℝ, z.M₁ < w → w < z.R₁ → ψ w ∈ α '' Icc 0 a
  L₂_real : (ψ z.L₂).im = 0
  L₂_mem : ψ z.L₂ ∈ β '' Icc 0 b
  R₁_real : (ψ z.R₁).im = 0
  R₁_mem : ψ z.R₁ ∈ α '' Icc 0 a
  J_mem : ψ z.R₂ ∈ α '' Icc 0 a ∩ β '' Icc 0 b
  tip₂ : ψ 0 = β b
  tip₁ : ψ z.M₁ = α a

namespace IsTouchZones

variable {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {z : ZW} (ht : IsTouchZones α a β b ψ z)
include ht

theorem L₂_lt_R₁ : z.L₂ < z.R₁ := by
  have hz := ht.good
  linarith [hz.L₂_le, hz.M₂_le, hz.R₂_le, hz.L₁_le, hz.M₁_le, ht.R₂_lt_M₁]

theorem L₂_le_zero : z.L₂ ≤ 0 := ht.M₂_eq ▸ ht.good.L₂_le

theorem zero_lt_M₁ : 0 < z.M₁ := ht.zero_lt_R₂.trans ht.R₂_lt_M₁

/-- **A chart point whose image is off the retained union lies in an untouched zone.** -/
theorem lt_or_gt_of_notMem {w : ℝ} (hw : ψ w ∉ α '' Icc 0 a ∪ β '' Icc 0 b) : w < z.L₂ ∨ z.R₁ < w := by
  have hz := ht.good
  by_contra hno
  push Not at hno
  obtain ⟨h1, h2⟩ := hno
  apply hw
  rcases h1.lt_or_eq with h1 | rfl
  swap
  · exact Or.inr ht.L₂_mem
  rcases h2.lt_or_eq with h2 | rfl
  swap
  · exact Or.inl ht.R₁_mem
  rcases lt_trichotomy w z.R₂ with h | rfl | h
  · exact Or.inr (ht.side₂ w h1 h)
  · exact Or.inl ht.J_mem.1
  · rcases lt_trichotomy w z.M₁ with h' | rfl | h'
    · exact Or.inl (ht.side₃ w (ht.junction ▸ h) h').1
    · rw [ht.tip₁]; exact Or.inl ⟨a, ⟨zero_le, le_rfl⟩, rfl⟩
    · exact Or.inl (ht.side₄ w h' h2)

end IsTouchZones

/-! ### The word clauses -/

variable {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {z : ZW}

/-- **The retained heights of the touching word** (`Supp7.IsRetainedWord`, Aux. lemma 86's (OF3)): at a chart real
whose image is an interior point of the retained union other than the two tips and the old common points, the word has
no jump there, the second prefix carries `∓λ − θ₂χ` on its left (`y < 0`) and right (`y > 0`) sides, and the first
prefix is right of `0` with one of its two side heights `∓λ − θ₁χ`. -/
theorem isRetainedWord_touchWord (ht : IsTouchZones α a β b ψ z) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (κ θ₁ θ₂ : ℝ) :
    IsRetainedWord κ θ₁ θ₂ α a β b ψ (z.word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₂ * QuantumZipper.chiC κ) (-sleLambda κ - θ₁ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₁ * QuantumZipper.chiC κ)).trunc := by
  have hz := ht.good
  intro y hyH hyβ hyα hyαβ
  have hyH' : 0 < (ψ y).im := hyH
  -- `y` is strictly inside `(L₂, R₁)` and is none of the five transition points
  have hyz₀ : ¬ y < z.L₂ := fun h => by linarith [(ht.zone₀ y h).1]
  have hyz₂ : ¬ z.R₁ < y := fun h => by linarith [(ht.zone₂ y h).1]
  have hyL₂ : y ≠ z.L₂ := by rintro rfl; linarith [ht.L₂_real]
  have hyR₁ : y ≠ z.R₁ := by rintro rfl; linarith [ht.R₁_real]
  have hy0 : y ≠ 0 := by rintro rfl; exact hyβ (by rw [ofReal_zero, ht.tip₂])
  have hyM₁ : y ≠ z.M₁ := by rintro rfl; exact hyα ht.tip₁
  have hyR₂ : y ≠ z.R₂ := by rintro rfl; exact hyαβ ht.J_mem
  have h1 : z.L₂ < y := lt_of_le_of_ne (not_lt.1 hyz₀) (Ne.symm hyL₂)
  have h2 : y < z.R₁ := lt_of_le_of_ne (not_lt.1 hyz₂) hyR₁
  have hyJ : y ∉ (z.word c₀ (-sleLambda κ - θ₂ * QuantumZipper.chiC κ) (sleLambda κ - θ₂ * QuantumZipper.chiC κ)
      (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)).trunc.jumps := by
    rw [BoundaryWord.trunc_jumps]
    intro hj
    obtain ⟨i, hi, hiy⟩ := BoundaryWord.mem_jumps.1 hj
    rcases hz.pos_cases hc₀ hi with h | h | h | h | h | h | ⟨j, -, hu, hT⟩
    · exact hyL₂ (hiy ▸ h)
    · exact hy0 (hiy ▸ h.trans ht.M₂_eq)
    · exact hyR₂ (hiy ▸ h)
    · exact hyR₂ (hiy ▸ h.trans ht.junction.symm)
    · exact hyM₁ (hiy ▸ h)
    · exact hyR₁ (hiy ▸ h)
    · have e : ψ y = ((c₀.2.1 j : ℝ) : ℂ) := by rw [← hiy, hT]; exact ht.T_spec _ hu
      rw [e] at hyH'
      simp at hyH'
  refine ⟨hy0, hyJ, fun hβ' => ?_, fun hα' => ?_⟩
  · refine ⟨fun hneg => ?_, fun hpos => ?_⟩
    · rw [BoundaryWord.trunc_fn]
      exact hz.fn_side₁ hc₀ h1 (ht.M₂_eq ▸ hneg)
    · have hyR : y < z.R₂ := by
        by_contra hge
        rcases (not_lt.1 hge).lt_or_eq with hgt | heq
        · rcases lt_or_gt_of_ne hyM₁ with h' | h'
          · exact (ht.side₃ y (ht.junction ▸ hgt) h').2 hβ'
          · exact hyαβ ⟨ht.side₄ y h' h2, hβ'⟩
        · exact hyR₂ heq.symm
      rw [BoundaryWord.trunc_fn]
      exact hz.fn_side₂ hc₀ (ht.M₂_eq ▸ hpos) hyR
  · -- on the first prefix: not on the second, so right of the junction
    have hyβ' : ψ y ∉ β '' Icc 0 b := fun h => hyαβ ⟨hα', h⟩
    have hJy : z.R₂ < y := by
      by_contra hle
      rcases (not_lt.1 hle).lt_or_eq with hlt | heq
      · exact hyβ' (ht.side₂ y h1 hlt)
      · exact hyR₂ heq
    refine ⟨ht.zero_lt_R₂.trans hJy, ?_⟩
    rcases lt_or_gt_of_ne hyM₁ with h | h
    · left
      rw [BoundaryWord.trunc_fn]
      exact hz.fn_side₃ hc₀ (ht.junction ▸ hJy) h
    · right
      rw [BoundaryWord.trunc_fn]
      exact hz.fn_side₄ hc₀ h h2

/-- **The untouched datum of the touching word** (`RLC.IsUntouchedWord`): at a chart real whose image is a real point
off the retained union and off the original jumps, the word has no jump and carries the original datum. -/
theorem isUntouchedWord_touchWord (ht : IsTouchZones α a β b ψ z) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) {bd : ℝ → ℝ} {J : Finset ℝ} (hc₀J : c₀.jumps = J)
    (hc₀b : ∀ y ∉ J, c₀.fn y = bd y) (g₁ g₂ g₃ g₄ : ℝ) :
    IsUntouchedWord bd J (α '' Icc 0 a ∪ β '' Icc 0 b) ψ (z.word c₀ g₁ g₂ g₃ g₄).trunc := by
  have hz := ht.good
  intro y hy0 hyA hyJ
  rw [BoundaryWord.trunc_jumps, BoundaryWord.trunc_fn]
  -- `y` is the chart point of the untouched real point `x = Re ψ(y)`
  have hzone : ((ψ y).re < z.a₂ ∨ z.b₁ < (ψ y).re) ∧ z.T (ψ y).re = y ∧ (y < z.L₂ ∨ z.R₁ < y) := by
    rcases ht.lt_or_gt_of_notMem hyA with h | h
    · obtain ⟨-, hx, hT⟩ := ht.zone₀ y h
      exact ⟨Or.inl hx, hT, Or.inl h⟩
    · obtain ⟨-, hx, hT⟩ := ht.zone₂ y h
      exact ⟨Or.inr hx, hT, Or.inr h⟩
  obtain ⟨hx, hT, hyz⟩ := hzone
  have hfn : (z.word c₀ g₁ g₂ g₃ g₄).fn y = c₀.fn (ψ y).re := by
    have key : (z.word c₀ g₁ g₂ g₃ g₄).fn (z.T (ψ y).re) = c₀.fn (ψ y).re := by
      rcases hx with h0 | h2
      · exact hz.fn_zone₀ hc₀ h0
      · exact hz.fn_zone₂ hc₀ h2
    rwa [hT] at key
  refine ⟨fun hj => ?_, hfn.trans (hc₀b _ hyJ)⟩
  obtain ⟨i, hi, hiy⟩ := BoundaryWord.mem_jumps.1 hj
  have hL₂R₁ : ∀ p, (p = z.L₂ ∨ p = z.M₂ ∨ p = z.R₂ ∨ p = z.L₁ ∨ p = z.M₁ ∨ p = z.R₁) → z.L₂ ≤ p ∧ p ≤ z.R₁ := by
    intro p hp
    have := ht.L₂_lt_R₁
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      constructor <;> linarith [hz.L₂_le, hz.M₂_le, hz.R₂_le, hz.L₁_le, hz.M₁_le]
  have hout : ¬ (z.L₂ ≤ y ∧ y ≤ z.R₁) := fun ⟨h1, h2⟩ => by
    rcases hyz with h | h <;> linarith
  rcases hz.pos_cases hc₀ hi with h | h | h | h | h | h | ⟨j, hjN, hu, hTj⟩
  · exact hout (hiy ▸ hL₂R₁ _ (Or.inl h))
  · exact hout (hiy ▸ hL₂R₁ _ (Or.inr (Or.inl h)))
  · exact hout (hiy ▸ hL₂R₁ _ (Or.inr (Or.inr (Or.inl h))))
  · exact hout (hiy ▸ hL₂R₁ _ (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact hout (hiy ▸ hL₂R₁ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact hout (hiy ▸ hL₂R₁ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · have e : (((c₀.2.1 j : ℝ) : ℂ)) = (((ψ y).re : ℝ) : ℂ) := by
      rw [← ht.T_spec _ hu, ← ht.T_spec _ hx]
      exact congrArg (fun w : ℝ => ψ w) (hTj.symm.trans (hiy.trans hT.symm))
    have e' : c₀.2.1 j = (ψ y).re := ofReal_injective e
    exact hyJ (hc₀J ▸ BoundaryWord.mem_jumps.2 ⟨j, hjN, e'⟩)

end RetTouch

end RLC

end InteractingSLE
