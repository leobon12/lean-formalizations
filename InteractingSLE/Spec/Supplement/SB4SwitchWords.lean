/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBWeights

/-!
# The hybrid middle word at an SB4 switch

Specification pp. 634–635; R53 Part D.6. Old upper-right sides give both
admissible groups; old upper-left sides and low connectors protect the lower
group. The separately retained original bridge keeps its assumed hybrid word.
All weight identities are reused from `SBWeights` and `S7Weights`.
-/

set_option autoImplicit false

open Set
open scoped NNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB

open Sec4 Supp7

/-- An exposed old upper-right side gives both admissible middle groups. -/
theorem switch_hybrid_old_right {κ φ ψ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hφθ : φ < θ) (hgap : |ψ - θ| < 2 * sleLambda κ / chiC κ) :
    -2 < cumWeightLeft κ ((sleLambda κ - θ * chiC κ) + φ * chiC κ) ∧
      -2 < cumWeightRight κ ((sleLambda κ - θ * chiC κ) + ψ * chiC κ) := by
  refine ⟨(sb21 hκ hκ4 hφθ).2.1, ?_⟩
  rw [(g6_old_right_weights hκ θ ψ).2]
  exact neg_two_lt_angleGap hκ hκ4 hgap

/-- An exposed old upper-left side gives the protected lower group, even when
its new upper-right group is inadmissible. -/
theorem switch_hybrid_old_left {κ φ ψ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hφθ : φ < θ) :
    -2 < cumWeightLeft κ ((-sleLambda κ - θ * chiC κ) + φ * chiC κ) ∧
      (-2 < cumWeightRight κ ((-sleLambda κ - θ * chiC κ) + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ ((-sleLambda κ - θ * chiC κ) + φ * chiC κ)) := by
  have hpos := (sb21 hκ hκ4 hφθ).2.2.2
  have hc : κ / 2 - 2 < 0 := by linarith only [hκ4]
  exact ⟨lt_trans (by norm_num) hpos, Or.inr (le_trans hc.le hpos.le)⟩

/-- A low connector has the same protected lower group; its actual original
height is used without replacing it by an ordinary-side height. -/
theorem switch_hybrid_low {κ φ ψ H : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hH : H ≤ -sleLambda κ - φ * chiC κ) :
    -2 < cumWeightLeft κ (H + φ * chiC κ) ∧
      (-2 < cumWeightRight κ (H + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (H + φ * chiC κ)) := by
  obtain ⟨hzero, hprotected⟩ := sb31 hκ hκ4 hH
  exact ⟨lt_of_lt_of_le (by norm_num) hzero, Or.inr hprotected.le⟩

/-- The exhaustive surviving-height classification in SB4 gives exactly SB1's
hybrid inequalities. `original` is the separately retained initial-bridge word.
The geometric and conditional-field assertion that these are all surviving
heights is an explicit hypothesis, not inferred from these arithmetic lemmas. -/
theorem switch_hybrid_of_height_types {κ φ ψ H : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {l : List (ℝ × ℝ≥0)} {original : Set ℝ}
    (hangles : ∀ p ∈ l, φ < p.1)
    (hgaps : ∀ p ∈ l, |ψ - p.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ B ∈ original, -2 < cumWeightLeft κ (B + φ * chiC κ) ∧
      (-2 < cumWeightRight κ (B + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (B + φ * chiC κ)))
    (htypes : (∃ p ∈ l, H = sleLambda κ - p.1 * chiC κ ∨
        H = -sleLambda κ - p.1 * chiC κ) ∨
      H ≤ -sleLambda κ - φ * chiC κ ∨ H ∈ original) :
    -2 < cumWeightLeft κ (H + φ * chiC κ) ∧
      (-2 < cumWeightRight κ (H + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (H + φ * chiC κ)) := by
  rcases htypes with ⟨p, hp, hH | hH⟩ | hH | hH
  · subst H
    obtain ⟨hL, hR⟩ := switch_hybrid_old_right hκ hκ4 (hangles p hp) (hgaps p hp)
    exact ⟨hL, Or.inl hR⟩
  · subst H
    exact switch_hybrid_old_left hκ hκ4 (hangles p hp)
  · exact switch_hybrid_low hκ hκ4 hH
  · exact hbridge H hH

/-- The pointwise height classification supplies the entire middle-word premise
for a specified new angle, including every retained original mark interval. -/
theorem switch_middle_word {κ φ ψ u v : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {l : List (ℝ × ℝ≥0)} {bc : ℝ → ℝ} {jc : Finset ℝ} {original : Set ℝ}
    (hangles : ∀ p ∈ l, φ < p.1)
    (hgaps : ∀ p ∈ l, |ψ - p.1| < 2 * sleLambda κ / chiC κ)
    (hbridge : ∀ B ∈ original, -2 < cumWeightLeft κ (B + φ * chiC κ) ∧
      (-2 < cumWeightRight κ (B + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (B + φ * chiC κ)))
    (htypes : ∀ x ∈ Ioo u v, x ∉ jc →
      (∃ p ∈ l, bc x = sleLambda κ - p.1 * chiC κ ∨
        bc x = -sleLambda κ - p.1 * chiC κ) ∨
      bc x ≤ -sleLambda κ - φ * chiC κ ∨ bc x ∈ original) :
    (∀ x ∈ Ioo u v, x ∉ jc → -2 < cumWeightLeft κ (bc x + φ * chiC κ)) ∧
      (∀ x ∈ Ioo u v, x ∉ jc →
        -2 < cumWeightRight κ (bc x + ψ * chiC κ) ∨
          κ / 2 - 2 ≤ cumWeightLeft κ (bc x + φ * chiC κ)) := by
  have hall := fun x hx hj =>
    switch_hybrid_of_height_types hκ hκ4 hangles hgaps hbridge (htypes x hx hj)
  exact ⟨fun x hx hj => (hall x hx hj).1, fun x hx hj => (hall x hx hj).2⟩

end InteractingSLE.Theorem14.SB
