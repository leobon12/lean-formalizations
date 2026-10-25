import Mathlib




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame

theorem measure_pair_union_le
    {Ω α : Type} [MeasurableSpace Ω] [DecidableEq α]
    (P : Measure Ω) (F : Finset α) (B : α → α → Set Ω) (q : ℝ≥0∞)
    (hB : ∀ z ∈ F, ∀ w ∈ F, P (B z w) ≤ q) :
    P (⋃ p ∈ F ×ˢ F, B p.1 p.2) ≤ (F.card : ℝ≥0∞) ^ 2 * q := by
  have hsum : (∑ p ∈ F ×ˢ F, P (B p.1 p.2)) ≤
      ∑ _p ∈ F ×ˢ F, q := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact hB p.1 hp1 p.2 hp2
  calc
    P (⋃ p ∈ F ×ˢ F, B p.1 p.2) ≤
        ∑ p ∈ F ×ˢ F, P (B p.1 p.2) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ F ×ˢ F, q := hsum
    _ = (F.card : ℝ≥0∞) ^ 2 * q := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_product]
      push_cast
      ring

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
