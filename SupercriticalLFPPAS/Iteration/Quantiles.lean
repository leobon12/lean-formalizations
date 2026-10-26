import Mathlib

/-! Finite counting for the two one-third quantiles in Proposition 5.1. -/

set_option autoImplicit false

namespace SupercriticalLFPPAS.Iteration

/-- The natural-number form of `ceil(n / 3)`. -/
def thirdQuantileIndex (n : ℕ) : ℕ := (n + 2) / 3

theorem thirdQuantileIndex_bounds (n : ℕ) :
    3 * thirdQuantileIndex n ≤ n + 2 ∧ n - 2 * (thirdQuantileIndex n - 1) ≥ thirdQuantileIndex n := by
  constructor <;> simp only [thirdQuantileIndex] <;> omega

/-- Two strict lower-quantile bounds leave at least a third of the radii in the open
interval between `k` and `k⁻¹`.  The hypotheses are the standard finite-count formulation
of both m-th-smallest values being greater than their respective thresholds. -/
theorem middle_card_of_two_small_tails {α : Type*} [DecidableEq α]
    (s : Finset α) (κ : α → ℝ) {k : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hlow : (s.filter fun r => κ r ≤ k).card < thirdQuantileIndex s.card)
    (hhigh : (s.filter fun r => k⁻¹ ≤ κ r).card < thirdQuantileIndex s.card) :
    (s.filter fun r => k < κ r ∧ κ r < k⁻¹).card ≥ thirdQuantileIndex s.card := by
  let low := s.filter fun r => κ r ≤ k
  let high := s.filter fun r => k⁻¹ ≤ κ r
  let middle := s.filter fun r => k < κ r ∧ κ r < k⁻¹
  have hkinv : k < k⁻¹ := by
    have h1 : (1 : ℝ) < k⁻¹ := by
      simpa [one_div] using one_div_lt_one_div_of_lt hk hk1
    exact hk1.trans h1
  have hdisj : Disjoint low high := by
    rw [Finset.disjoint_left]
    intro r hL hH
    simp only [low, Finset.mem_filter] at hL
    simp only [high, Finset.mem_filter] at hH
    have hL' : κ r ≤ k := hL.2
    have hH' : k⁻¹ ≤ κ r := hH.2
    linarith
  have hpart : s \ (low ∪ high) = middle := by
    ext r
    simp only [Finset.mem_sdiff, Finset.mem_union, low, high, middle, Finset.mem_filter]
    constructor
    · rintro ⟨hr, hnot⟩
      have hlow' : ¬ κ r ≤ k := by
        intro h
        exact hnot (Or.inl ⟨hr, h⟩)
      have hhigh' : ¬ k⁻¹ ≤ κ r := by
        intro h
        exact hnot (Or.inr ⟨hr, h⟩)
      exact ⟨hr, lt_of_not_ge hlow', lt_of_not_ge hhigh'⟩
    · rintro ⟨hr, hlow', hhigh'⟩
      refine ⟨hr, ?_⟩
      intro hbad
      rcases hbad with hL | hH
      · exact (not_le_of_gt hlow') hL.2
      · exact (not_le_of_gt hhigh') hH.2
  have hlowCard : low.card < thirdQuantileIndex s.card := by
    simpa [low] using hlow
  have hhighCard : high.card < thirdQuantileIndex s.card := by
    simpa [high] using hhigh
  have hsubset : low ∪ high ⊆ s := by
    intro r hr
    rcases Finset.mem_union.mp hr with hL | hH
    · exact (Finset.mem_filter.mp hL).1
    · exact (Finset.mem_filter.mp hH).1
  have hcard : (s \ (low ∪ high)).card + (low ∪ high).card = s.card :=
    Finset.card_sdiff_add_card_eq_card hsubset
  have hunion : (low ∪ high).card = low.card + high.card := Finset.card_union_of_disjoint hdisj
  have hn := (thirdQuantileIndex_bounds s.card).1
  have hmiddle : middle.card ≥ thirdQuantileIndex s.card := by
    rw [← hpart]
    omega
  simpa [middle] using hmiddle

/-- For positive scale ratios, a small inverse is the same as a large original ratio. -/
theorem inverse_le_iff_reciprocal_le {κ k : ℝ} (hκ : 0 < κ) (hk : 0 < k) :
    κ⁻¹ ≤ k ↔ k⁻¹ ≤ κ := by
  rw [inv_le_iff_one_le_mul₀ hκ, inv_le_iff_one_le_mul₀ hk]
  simp [mul_comm]

/-- Quantile pigeonhole in the source form: the `m`-th smallest value of both `κ` and
`κ⁻¹` exceeds `k`, expressed by the equivalent strict tail-count conditions. -/
theorem middle_card_of_two_inverse_quantiles {α : Type*} [DecidableEq α]
    (s : Finset α) (κ : α → ℝ) {k : ℝ} (hk : 0 < k) (hk1 : k < 1)
    (hκ : ∀ r ∈ s, 0 < κ r)
    (hlow : (s.filter fun r => κ r ≤ k).card < thirdQuantileIndex s.card)
    (hhigh : (s.filter fun r => (κ r)⁻¹ ≤ k).card < thirdQuantileIndex s.card) :
    (s.filter fun r => k < κ r ∧ κ r < k⁻¹).card ≥ thirdQuantileIndex s.card := by
  have hset : (s.filter fun r => (κ r)⁻¹ ≤ k) =
      (s.filter fun r => k⁻¹ ≤ κ r) := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hr, h⟩
      exact ⟨hr, (inverse_le_iff_reciprocal_le (hκ r hr) hk).mp h⟩
    · rintro ⟨hr, h⟩
      exact ⟨hr, (inverse_le_iff_reciprocal_le (hκ r hr) hk).mpr h⟩
  have hhigh' : (s.filter fun r => k⁻¹ ≤ κ r).card < thirdQuantileIndex s.card := by
    rw [← hset]
    exact hhigh
  exact middle_card_of_two_small_tails s κ hk hk1 hlow hhigh'

/-- The finite pigeonhole inequality used after selecting `n` radii. -/
theorem good_radii_count_bound (n : ℕ) :
    n - 2 * (thirdQuantileIndex n - 1) ≥ thirdQuantileIndex n :=
  (thirdQuantileIndex_bounds n).2

end SupercriticalLFPPAS.Iteration
