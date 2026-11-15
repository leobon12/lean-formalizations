/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCondDetHistDisj
import InteractingSLE.Spec.Supplement.RetTouchZones

/-!
# Leaf 3, the first continuation: the SIDED outer word of the first path

Packet PROVE-T15-ORDDET3 (Theorem 1.5's leaf 3, `RLC.RetOrdDetFstStatement`; Aux. lemmas 85–86, supplement
pp. 299–301; Lemma 7.6's zone word, PROVE-LEMMA76G).

`Supp7.IsRetainedWord` records the side heights of the FIRST path only up to sides ("`c(y)` is one of `∓λ − θ₁χ`"),
because the retained chart is centred at the second tip. The first continuation needs the sided form: in the retained
chart, the first prefix's left side lies left of the first tip's chart point `tipPos` and carries `−λ − θ₁χ`, its
right side lies right of it and carries `λ − θ₁χ`. This file defines that form and proves it for the two explicit
words of an ordinary pair:

* **`IsRetainedWordFst`**: the sided first-path heights relative to a chart point `τ`;
* **`isRetainedWordFst_zoneWord`**: Lemma 7.6's zone word at a disjoint pair (relative to the zone point `M₁`);
* **`isRetainedWordFst_touchWord`**: the touching word at a touching pair with Aux. lemma 85's zones (relative to
  `M₁`).

Both `M₁` are `chartPt` of the first tip, i.e. `tipPos` (the forward chart limit at the first tip).

For Theorem 1.5; deterministic (R43/R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace RLC

open Supp7 Restart

/-- **The sided outer word of the first path** relative to a chart point `τ` (the first tip's chart point): every real
`y` whose chart image is an interior point of the first prefix, off the second prefix and not the first tip, carries
the left-side height `−λ − θ₁χ` if `y < τ` and the right-side height `λ − θ₁χ` if `τ < y`. -/
def IsRetainedWordFst (κ θ₁ : ℝ) (α : ℝ≥0 → ℂ) (a : ℝ≥0) (β : ℝ≥0 → ℂ) (b : ℝ≥0) (ψ : ℂ → ℂ) (τ : ℝ)
    (c : BoundaryWord) : Prop :=
  ∀ y : ℝ, ψ y ∈ H → ψ y ≠ α a → ψ y ∈ α '' Icc 0 a → ψ y ∉ β '' Icc 0 b →
    (y < τ → c.fn y = -sleLambda κ - θ₁ * QuantumZipper.chiC κ) ∧
      (τ < y → c.fn y = sleLambda κ - θ₁ * QuantumZipper.chiC κ)

section Zone

open Sec7.Lemma76G

variable {α β : ℝ≥0 → ℂ} {ζ₁ ζ₂ : ℝ≥0∞} {x₁ x₂ : ℝ} {a b : ℝ≥0} {φ ψ : ℂ → ℂ} {lift : ℂ → ℝ}

/-- **The sided first-path heights of Lemma 7.6's zone word at a disjoint pair.** -/
theorem isRetainedWordFst_zoneWord (hs : IsSetting α ζ₁ x₁ a β ζ₂ x₂ b φ ψ lift) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (κ θ₁ : ℝ) (g₁ g₂ : ℝ) :
    IsRetainedWordFst κ θ₁ α a β b ψ (zoneData φ α a β b).M₁ ((zoneData φ α a β b).word c₀ g₁ g₂
      (-sleLambda κ - θ₁ * QuantumZipper.chiC κ) (sleLambda κ - θ₁ * QuantumZipper.chiC κ)).trunc := by
  set z := zoneData φ α a β b with hzdef
  have hz := hs.zoneData_good
  intro y hyH hyα hα' _
  have hyH' : 0 < (ψ y).im := hyH
  have hyL₁ : y ≠ z.L₁ := by rintro rfl; linarith [(im_inv_R₂_L₁ hs).2]
  have hyR₁ : y ≠ z.R₁ := by rintro rfl; linarith [im_inv_R₁ hs]
  have h1 : z.L₁ < y := lt_of_le_of_ne (hs.L₁_le_of_mem₁ hα') (Ne.symm hyL₁)
  have h2 : y < z.R₁ := lt_of_le_of_ne (hs.le_R₁_of_mem₁ hα') hyR₁
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [BoundaryWord.trunc_fn]
    exact ZW.fn_side₃ hz hc₀ h1 h
  · rw [BoundaryWord.trunc_fn]
    exact ZW.fn_side₄ hz hc₀ h h2

end Zone

section Touch

open RetTouch Sec7.Lemma76G

variable {α β : ℝ≥0 → ℂ} {a b : ℝ≥0} {ψ : ℂ → ℂ} {z : Sec7.Lemma76G.ZW}

/-- **The sided first-path heights of the touching word** (Aux. lemma 85's zones (OF2)). -/
theorem isRetainedWordFst_touchWord (ht : IsTouchZones α a β b ψ z) {c₀ : BoundaryWord}
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) (κ θ₁ : ℝ) (g₁ g₂ : ℝ) :
    IsRetainedWordFst κ θ₁ α a β b ψ z.M₁ (z.word c₀ g₁ g₂ (-sleLambda κ - θ₁ * QuantumZipper.chiC κ)
      (sleLambda κ - θ₁ * QuantumZipper.chiC κ)).trunc := by
  have hz := ht.good
  intro y hyH _ hα' hyβ'
  have hyH' : 0 < (ψ y).im := hyH
  have hyz₂ : ¬ z.R₁ < y := fun h => by linarith [(ht.zone₂ y h).1]
  have hyR₁ : y ≠ z.R₁ := by rintro rfl; linarith [ht.R₁_real]
  have h2 : y < z.R₁ := lt_of_le_of_ne (not_lt.1 hyz₂) hyR₁
  have hyz₀ : ¬ y < z.L₂ := fun h => by linarith [(ht.zone₀ y h).1]
  have hyL₂ : y ≠ z.L₂ := by rintro rfl; linarith [ht.L₂_real]
  have h1 : z.L₂ < y := lt_of_le_of_ne (not_lt.1 hyz₀) (Ne.symm hyL₂)
  have hJy : z.R₂ < y := by
    by_contra hle
    rcases (not_lt.1 hle).lt_or_eq with hlt | heq
    · exact hyβ' (ht.side₂ y h1 hlt)
    · exact hyβ' (heq ▸ ht.J_mem.2)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [BoundaryWord.trunc_fn]
    exact hz.fn_side₃ hc₀ (ht.junction ▸ hJy) h
  · rw [BoundaryWord.trunc_fn]
    exact hz.fn_side₄ hc₀ h h2

end Touch

end RLC

end InteractingSLE
