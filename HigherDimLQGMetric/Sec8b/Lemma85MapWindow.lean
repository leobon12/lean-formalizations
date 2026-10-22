import HigherDimLQGMetric.Sec8b.Lemma85TrapStep

/-! Return a (T3) shortcut on an affine piece to the original geodesic. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem s7b_map_shortcut_window (D E : ContMetric d)
    (P R : ℝ → Rd d) (B : Set (Rd d))
    {a b τ₁ τ₂ ℓ c' : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hinside : ∀ t ∈ Icc a b, P t ∈ B)
    (hRform : ∀ t ∈ Icc (0 : ℝ) 1,
      R t = P (a + t * (b - a)))
    (hτ₁ : 0 ≤ τ₁) (hτ₁₂ : τ₁ ≤ τ₂) (hτ₂ : τ₂ ≤ 1)
    (hcost : ENNReal.ofReal ℓ ≤ D.len R τ₁ τ₂)
    (hshort : E.internal B (R τ₁) (R τ₂) ≤
      ENNReal.ofReal c' * D.len R τ₁ τ₂) :
    ∃ t₁ t₂ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ t₂ ∧ t₂ ≤ 1 ∧
      (∀ t ∈ Icc t₁ t₂, P t ∈ B) ∧
      ENNReal.ofReal ℓ ≤ D.len P t₁ t₂ ∧
      E.internal B (P t₁) (P t₂) ≤
        ENNReal.ofReal c' * D.len P t₁ t₂ := by
  let t₁ := a + τ₁ * (b - a)
  let t₂ := a + τ₂ * (b - a)
  have ht₁ : a ≤ t₁ := by
    dsimp [t₁]
    have hm := mul_nonneg hτ₁ (sub_nonneg.mpr hab)
    linarith only [hm]
  have ht₂ : t₂ ≤ b := by
    dsimp [t₂]
    have hm := mul_le_mul_of_nonneg_right hτ₂ (sub_nonneg.mpr hab)
    nlinarith only [hm]
  have ht₁₂ : t₁ ≤ t₂ := by
    dsimp [t₁, t₂]
    simpa only [add_comm] using
      (add_le_add_left
        (mul_le_mul_of_nonneg_right hτ₁₂ (sub_nonneg.mpr hab)) a)
  have hRτ₁ : R τ₁ = P t₁ := hRform τ₁ ⟨hτ₁, hτ₁₂.trans hτ₂⟩
  have hRτ₂ : R τ₂ = P t₂ := hRform τ₂ ⟨hτ₁.trans hτ₁₂, hτ₂⟩
  have hlen : D.len R τ₁ τ₂ = D.len P t₁ t₂ :=
    s7b_affine_piece_len D P R hab hτ₁ hτ₁₂ hτ₂ hRform
  refine ⟨t₁, t₂, ha.trans ht₁, ht₁₂, ht₂.trans hb, ?_, ?_, ?_⟩
  · intro t ht
    exact hinside t ⟨ht₁.trans ht.1, ht.2.trans ht₂⟩
  · rw [hlen] at hcost
    exact hcost
  · rw [hRτ₁, hRτ₂, hlen] at hshort
    exact hshort

end HigherDimLQGMetric
