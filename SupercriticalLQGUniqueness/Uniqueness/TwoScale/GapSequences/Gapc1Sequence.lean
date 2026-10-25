import Mathlib




 








set_option autoImplicit false

open Finset

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapSequences

theorem sum_Ioc_succ_self (X : ℕ → ℝ) (m : ℕ) : ∑ j ∈ Ioc m (m + 1), X j = X (m + 1) := by
  rw [Finset.sum_Ioc_succ_top le_rfl, Finset.Ioc_self, Finset.sum_empty, zero_add]

 

theorem pow_mul_le_tail (c : ℝ) (hc : 0 < c) (N : ℕ) (X : ℕ → ℝ) (_hX : ∀ i, 0 ≤ X i)
    (hclaim : ∀ i, 1 ≤ i → i < N → c * ∑ j ∈ Ioc i N, X j ≤ X i) :
    ∀ k, k + 2 ≤ N → (1 + c) ^ k * X N ≤ ∑ j ∈ Ioc (N - k - 1) N, X j := by
  intro k
  induction k with
  | zero =>
    intro hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_cancel]
    rw [sum_Ioc_succ_self]
  | succ k ih =>
    intro hN
    have ih' := ih (by omega)
    set m := N - (k + 1) - 1 with hm
    have hm1 : m + 1 = N - k - 1 := by omega
    have hsplit : ∑ j ∈ Ioc m N, X j = X (m + 1) + ∑ j ∈ Ioc (m + 1) N, X j := by
      rw [← Finset.sum_Ioc_consecutive X (Nat.le_succ m) (by omega), sum_Ioc_succ_self]
    have hcl := hclaim (m + 1) (by omega) (by omega)
    rw [hsplit, hm1]
    rw [hm1] at hcl
    calc (1 + c) ^ (k + 1) * X N = (1 + c) * ((1 + c) ^ k * X N) := by ring
      _ ≤ (1 + c) * ∑ j ∈ Ioc (N - k - 1) N, X j := by gcongr
      _ = c * ∑ j ∈ Ioc (N - k - 1) N, X j + ∑ j ∈ Ioc (N - k - 1) N, X j := by ring
      _ ≤ X (N - k - 1) + ∑ j ∈ Ioc (N - k - 1) N, X j := by gcongr

 
theorem seq_ratio (c : ℝ) (hc : 0 < c) (N : ℕ) (hN : 2 ≤ N) (X : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i)
    (hclaim : ∀ i, 1 ≤ i → i < N → c * ∑ j ∈ Ioc i N, X j ≤ X i) :
    c * (1 + c) ^ (N - 2) * X N ≤ X 1 := by
  have h := pow_mul_le_tail c hc N X hX hclaim (N - 2) (by omega)
  have hidx : N - (N - 2) - 1 = 1 := by omega
  rw [hidx] at h
  calc c * (1 + c) ^ (N - 2) * X N = c * ((1 + c) ^ (N - 2) * X N) := by ring
    _ ≤ c * ∑ j ∈ Ioc 1 N, X j := by gcongr
    _ ≤ X 1 := hclaim 1 le_rfl (by omega)

 
theorem seq_ratio_Y (c : ℝ) (hc : 0 < c) (N : ℕ) (hN : 2 ≤ N) (X : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i)
    (hclaim : ∀ i, 1 ≤ i → i < N → c * ∑ j ∈ Ioc i N, X j ≤ X i) (Y : ℝ)
    (hY : X 1 ≤ c⁻¹ * Y) :
    X N * (1 + c) ^ (N - 2) ≤ c⁻¹ * c⁻¹ * Y := by
  have h := (seq_ratio c hc N hN X hX hclaim).trans hY
  calc X N * (1 + c) ^ (N - 2) = c⁻¹ * (c * (1 + c) ^ (N - 2) * X N) := by
        field_simp
    _ ≤ c⁻¹ * (c⁻¹ * Y) := by gcongr
    _ = c⁻¹ * c⁻¹ * Y := by ring

 
theorem scale_fact_one (δ l : ℝ) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (hl1 : δ ≤ l)
    (hl2 : l < 2 * δ) : l ^ ((3 : ℝ) / 4) ≤ δ ^ ((1 : ℝ) / 2) := by
  have hl0 : 0 < l := hδ.trans_le hl1
  have h1 : l ^ ((3 : ℝ) / 4) ≤ (2 * δ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hl0.le hl2.le (by norm_num)
  have h8 : (2 : ℝ) ^ ((3 : ℝ) / 4) = (8 : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h2 : (2 * δ) ^ ((3 : ℝ) / 4) = (8 * δ) ^ ((1 : ℝ) / 4) * δ ^ ((1 : ℝ) / 2) := by
    rw [Real.mul_rpow (by norm_num) hδ.le, Real.mul_rpow (by norm_num) hδ.le, h8, mul_assoc,
      ← Real.rpow_add hδ]
    norm_num
  have h3 : (8 * δ) ^ ((1 : ℝ) / 4) ≤ 1 :=
    Real.rpow_le_one (by positivity) (by linarith) (by norm_num)
  have h4 : 0 ≤ δ ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hδ.le _
  calc l ^ ((3 : ℝ) / 4) ≤ (2 * δ) ^ ((3 : ℝ) / 4) := h1
    _ = (8 * δ) ^ ((1 : ℝ) / 4) * δ ^ ((1 : ℝ) / 2) := h2
    _ ≤ 1 * δ ^ ((1 : ℝ) / 2) := by gcongr
    _ = δ ^ ((1 : ℝ) / 2) := one_mul _

 

theorem scale_fact_two (δ l β : ℝ) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hl1 : δ ≤ l)
    (hl2 : l < 2 * δ) (hβ : 0 < β) : l ^ β ≤ δ ^ (β / 2) := by
  have hl0 : 0 < l := hδ.trans_le hl1
  have h1 : l ^ β ≤ (2 * δ) ^ β := Real.rpow_le_rpow hl0.le hl2.le hβ.le
  have h2 : (2 * δ) ^ β = ((2 * δ) ^ (2 : ℝ)) ^ (β / 2) := by
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have h3 : (2 * δ) ^ (2 : ℝ) ≤ δ := by
    rw [Real.rpow_two]
    nlinarith
  calc l ^ β ≤ (2 * δ) ^ β := h1
    _ = ((2 * δ) ^ (2 : ℝ)) ^ (β / 2) := h2
    _ ≤ δ ^ (β / 2) := Real.rpow_le_rpow (by positivity) h3 (by positivity)

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapSequences

