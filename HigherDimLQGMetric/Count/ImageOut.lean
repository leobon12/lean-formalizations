import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Counting the distinct outputs of a finite pruning rule.
-/

set_option autoImplicit false

namespace HigherDimLQGMetric

private theorem pow_mul_descFactorial_le {N k m : ℕ} (hmk : m ≤ k) (hkN : k ≤ N) :
    N ^ m * k.descFactorial m ≤ k ^ m * N.descFactorial m := by
  rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range]
  have hprod : (∏ i ∈ Finset.range m, N * (k - i)) ≤
      ∏ i ∈ Finset.range m, k * (N - i) := by
    apply Finset.prod_le_prod
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    have hik : i ≤ k := by omega
    have hiN : i ≤ N := by omega
    have hki : k - i + i = k := Nat.sub_add_cancel hik
    have hNi : N - i + i = N := Nat.sub_add_cancel hiN
    nlinarith
  simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] using hprod

private theorem pow_mul_choose_le {N k m : ℕ} (hmk : m ≤ k) (hkN : k ≤ N) :
    N ^ m * k.choose m ≤ k ^ m * N.choose m := by
  have h := pow_mul_descFactorial_le hmk hkN
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at h
  have hfac : 0 < m.factorial := Nat.factorial_pos m
  nlinarith

/-- The abstract counting step of Lemma 8.4. -/
theorem card_image_out_ge {α : Type*} [DecidableEq α] (s : Finset α) {k m : ℕ} (hmk : m ≤ k)
    (hks : k ≤ s.card) (out : Finset α → Finset α)
    (hout : ∀ t ∈ s.powersetCard k, out t ⊆ t ∧ m ≤ (out t).card) :
    ((s.card : ℝ) / k) ^ m ≤ ((s.powersetCard k).image out).card := by
  classical
  let T := s.powersetCard k
  let O := T.image out
  have ho_s : ∀ o ∈ O, o ⊆ s := by
    intro o ho
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ho
    exact (hout t ht).1.trans (Finset.mem_powersetCard.mp ht).1
  have ho_m : ∀ o ∈ O, m ≤ o.card := by
    intro o ho
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ho
    exact (hout t ht).2
  have ho_k : ∀ o ∈ O, o.card ≤ k := by
    intro o ho
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ho
    exact (Finset.card_le_card (hout t ht).1).trans_eq (Finset.mem_powersetCard.mp ht).2
  have hfiber : ∀ o ∈ O, (T.filter (fun t => out t = o)).card ≤
      (s.card - m).choose (k - m) := by
    intro o ho
    have hsubset : T.filter (fun t => out t = o) ⊆
        T.filter (fun t => o ⊆ t) := by
      intro t ht
      have htT := (Finset.mem_filter.mp ht).1
      have hto := (Finset.mem_filter.mp ht).2
      exact Finset.mem_filter.mpr ⟨htT, hto ▸ (hout t htT).1⟩
    have hcount : (T.filter (fun t => o ⊆ t)).card =
        (s.card - o.card).choose (k - o.card) := by
      exact Finset.card_filter_powersetCard_subset o s k (ho_s o ho) (ho_k o ho)
    have hchoose : (s.card - o.card).choose (k - o.card) ≤
        (s.card - m).choose (k - m) := by
      have hok := ho_k o ho
      have hom := ho_m o ho
      have hos := Finset.card_le_card (ho_s o ho)
      have hsymo : (s.card - o.card).choose (k - o.card) =
          (s.card - o.card).choose (s.card - k) := by
        have heq : (s.card - o.card) - (k - o.card) = s.card - k := by omega
        rw [← heq]
        exact (Nat.choose_symm (by omega)).symm
      have hsymm : (s.card - m).choose (k - m) =
          (s.card - m).choose (s.card - k) := by
        have heq : (s.card - m) - (k - m) = s.card - k := by omega
        rw [← heq]
        exact (Nat.choose_symm (by omega)).symm
      rw [hsymo, hsymm]
      exact Nat.choose_le_choose _ (by omega)
    exact (Finset.card_le_card hsubset).trans (hcount.le.trans hchoose)
  have hdouble : s.card.choose k ≤
      (s.card - m).choose (k - m) * O.card := by
    simpa [T, O, Finset.card_powersetCard] using
      Finset.card_le_mul_card_image T ((s.card - m).choose (k - m)) hfiber
  have hident : s.card.choose k * k.choose m =
      s.card.choose m * (s.card - m).choose (k - m) :=
    Nat.choose_mul hmk
  have hCpos : 0 < (s.card - m).choose (k - m) := Nat.choose_pos (by omega)
  have hchoose : s.card.choose m ≤ O.card * k.choose m := by
    have h := Nat.mul_le_mul_right (k.choose m) hdouble
    rw [hident] at h
    nlinarith
  have hpow := pow_mul_choose_le hmk hks
  by_cases hkzero : k = 0
  · have hm0 : m = 0 := by omega
    subst k
    subst m
    have hO : 1 ≤ O.card := by
      simpa only [Nat.choose_zero_right, Nat.sub_zero, Nat.mul_one, one_mul] using hdouble
    simpa only [div_zero, pow_zero] using
      (show (1 : ℝ) ≤ O.card by exact_mod_cast hO)
  have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
  have hchoosepos : 0 < k.choose m := Nat.choose_pos hmk
  have hNpow : (s.card : ℝ) ^ m ≤ (k : ℝ) ^ m * O.card := by
    have hpowR : ((s.card ^ m * k.choose m : ℕ) : ℝ) ≤
        ((k ^ m * s.card.choose m : ℕ) : ℝ) := Nat.cast_le.mpr hpow
    have hchooseR : ((s.card.choose m : ℕ) : ℝ) ≤
        (O.card : ℝ) * (k.choose m : ℝ) := by exact_mod_cast hchoose
    have hkpow : 0 ≤ (k : ℝ) ^ m := by positivity
    have hkc : 0 < (k.choose m : ℝ) := by exact_mod_cast hchoosepos
    push_cast at hpowR
    nlinarith [mul_nonneg (sub_nonneg.mpr hchooseR) hkpow]
  have hkpowpos : 0 < (k : ℝ) ^ m := pow_pos (by exact_mod_cast hkpos) _
  rw [div_pow]
  apply (div_le_iff₀ hkpowpos).2
  simpa only [mul_comm] using hNpow

end HigherDimLQGMetric
