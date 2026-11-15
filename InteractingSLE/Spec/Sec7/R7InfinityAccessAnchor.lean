/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityAccessReal

/-!
# A real lift access stays outside the compact two-arm boundary

PROVE-R7-GAPEQ. A real access outside the pole-to-gates interval compactifies to a
nonzero real access outside the joining segment and both open half-plane arms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdMap)

namespace InteractingSLE.Sec7.R7InfinityAccess

open Sec6 R7InfinityChart

/-- The only real points of the compact boundary are its joining segment and
the target zero. -/
theorem real_not_mem_compactBoundary {b₁ b₂ : ℝ → ℂ} {x₁ x₂ x : ℝ}
    (hz₁ : b₁ 0 = x₁) (hz₂ : b₂ 0 = x₂) (ho₁ : b₁ 1 = 0) (ho₂ : b₂ 1 = 0)
    (hH₁ : ∀ v ∈ Ioo (0 : ℝ) 1, b₁ v ∈ H) (hH₂ : ∀ v ∈ Ioo (0 : ℝ) 1, b₂ v ∈ H)
    (hx0 : x ≠ 0) (hx : x ∉ Icc (min x₁ x₂) (max x₁ x₂)) :
    (x : ℂ) ∉ compactBoundary b₁ b₂ x₁ x₂ := by
  have harm : ∀ {b : ℝ → ℂ} {q : ℝ}, b 0 = q → b 1 = 0 →
      (∀ v ∈ Ioo (0 : ℝ) 1, b v ∈ H) → q ∈ Icc (min x₁ x₂) (max x₁ x₂) →
      (x : ℂ) ∉ b '' Icc 0 1 := by
    intro b q hz ho hH hq hb
    rcases arcInf_real hz ho hH hb (ofReal_im x) with he | he
    · exact hx (ofReal_injective he ▸ hq)
    · exact hx0 (ofReal_eq_zero.1 he)
  rintro ((hx₁ | hx₂) | ⟨y, hy, he⟩)
  · exact harm hz₁ ho₁ hH₁ ⟨min_le_left _ _, le_max_left _ _⟩ hx₁
  · exact harm hz₂ ho₂ hH₂ ⟨min_le_right _ _, le_max_right _ _⟩ hx₂
  · exact hx (ofReal_injective he ▸ hy)

/-- A real lift access outside the finite pole-to-gates interval supplies the
compact exterior access used in side selection. -/
theorem compact_access_of_real_lift {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {E : Set ℂ} {s a q₁ q₂ : ℝ} {b₁ b₂ : ℝ → ℂ}
    (hb₁ : IsLastVisitArm W η A₁ s a q₁ b₁) (hb₂ : IsLastVisitArm W η A₂ s a q₂ b₂)
    (ha : a < min q₁ q₂)
    (hreal : ∃ y : ℝ, y ∉ Icc a (max q₁ q₂) ∧ (y : ℂ) ∈ closure (fwdMap W s '' E)) :
    ∃ x : ℝ, (x : ℂ) ∈ closure (psiMap a '' (fwdMap W s '' E)) ∧
      (x : ℂ) ∉ compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹) := by
  obtain ⟨y, hy, hycl⟩ := hreal
  have haq₁ := ha.trans_le (min_le_left _ _)
  have haq₂ := ha.trans_le (min_le_right _ _)
  have hya : y ≠ a := by
    intro he
    apply hy
    rw [he]
    exact ⟨le_rfl, haq₁.le.trans (le_max_left _ _)⟩
  have hyc : (y : ℂ) ≠ a := fun he => hya (ofReal_injective he)
  have hm := (continuousOn_psiMap.continuousAt
    (isOpen_compl_singleton.mem_nhds hyc)).continuousWithinAt.mem_closure_image hycl
  rw [psiMap_ofReal] at hm
  refine ⟨-(y - a)⁻¹, hm, real_not_mem_compactBoundary hb₁.2.2.1 hb₂.2.2.1
    hb₁.2.2.2.1 hb₂.2.2.2.1 hb₁.2.2.2.2.1 hb₂.2.2.2.2.1
    (neg_ne_zero.2 (inv_ne_zero (sub_ne_zero.2 hya))) ?_⟩
  by_cases hlt : y < a
  · have hx : 0 < -(y - a)⁻¹ := neg_pos.2 (inv_lt_zero'.2 (sub_neg.2 hlt))
    have hx₁ : -(q₁ - a)⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 (sub_pos.2 haq₁))
    have hx₂ : -(q₂ - a)⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 (sub_pos.2 haq₂))
    exact fun h => (not_le.2 ((max_lt hx₁ hx₂).trans hx)) h.2
  · have hqy : max q₁ q₂ < y := lt_of_not_ge fun h => hy ⟨not_lt.1 hlt, h⟩
    have hx₁ := (psiMap_ofReal_lt haq₁ ((le_max_left _ _).trans_lt hqy)).1
    have hx₂ := (psiMap_ofReal_lt haq₂ ((le_max_right _ _).trans_lt hqy)).1
    exact fun h => (not_le.2 (max_lt hx₁ hx₂)) h.2

end InteractingSLE.Sec7.R7InfinityAccess
