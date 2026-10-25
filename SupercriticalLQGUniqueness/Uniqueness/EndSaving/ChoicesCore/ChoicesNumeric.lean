import SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingCore.Section4Counting
import Mathlib.Data.Nat.Choose.Bounds




 






set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.ChoicesCore

private theorem half_le_sub_choose {n k : ℕ} (hk : 2 * k ≤ n) :
    (n : ℝ) / 2 ≤ (n + 1 - k : ℕ) := by
  have h : n ≤ 2 * (n + 1 - k) := by omega
  have hreal : (n : ℝ) ≤ 2 * ((n + 1 - k : ℕ) : ℝ) := by
    exact_mod_cast h
  linarith only [hreal]

 
theorem choose_lower_half (n k : ℕ) (hk : 2 * k ≤ n) :
    (n : ℝ) ^ k / (2 ^ k * (k.factorial : ℝ)) ≤ (n.choose k : ℝ) := by
  have hhalf : (n : ℝ) / 2 ≤ (n + 1 - k : ℕ) := half_le_sub_choose hk
  have hpow : ((n : ℝ) / 2) ^ k ≤ ((n + 1 - k : ℕ) : ℝ) ^ k := by
    gcongr
  have hbound : (((n + 1 - k : ℕ) : ℝ) ^ k) / (k.factorial : ℝ) ≤
      (n.choose k : ℝ) := Nat.pow_le_choose k n
  calc
    (n : ℝ) ^ k / (2 ^ k * (k.factorial : ℝ)) =
        ((n : ℝ) / 2) ^ k / (k.factorial : ℝ) := by
      rw [div_pow]
      ring
    _ ≤ (((n + 1 - k : ℕ) : ℝ) ^ k) / (k.factorial : ℝ) := by
      exact div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ (n.choose k : ℝ) := hbound

 

theorem stableSubset_image_poly {α : Type*} [DecidableEq α]
    (S : Finset α) (k m : ℕ) (Φ : Finset α → Finset α)
    (hk : 2 * k ≤ S.card) (hkpos : 0 < k) (hmk : m ≤ k)
    (hsub : ∀ A ∈ S.powersetCard k, Φ A ⊆ A)
    (hcard : ∀ A ∈ S.powersetCard k, m ≤ (Φ A).card) :
    (((k - m).factorial : ℝ) / (2 ^ k * (k.factorial : ℝ))) *
        (S.card : ℝ) ^ (k - (k - m)) ≤
      (((S.powersetCard k).image Φ).card : ℝ) := by
  let n := S.card
  let s := k - m
  let I := ((S.powersetCard k).image Φ).card
  have hs : s ≤ k := Nat.sub_le _ _
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfiber := EndSaving.CountingCore.stableSubset_image_count S k m Φ hk hmk hsub hcard
  have hfiberR : (n.choose k : ℝ) ≤ (n.choose s : ℝ) * I := by
    exact_mod_cast hfiber
  have hupper : (n.choose s : ℝ) ≤ (n : ℝ) ^ s / (s.factorial : ℝ) :=
    Nat.choose_le_pow_div s n
  have hI : (0 : ℝ) ≤ I := by positivity
  have hbound : (n : ℝ) ^ k / (2 ^ k * (k.factorial : ℝ)) ≤
      ((n : ℝ) ^ s / (s.factorial : ℝ)) * I :=
    (choose_lower_half n k hk).trans (hfiberR.trans
      (mul_le_mul_of_nonneg_right hupper hI))
  have hpow : (n : ℝ) ^ k = (n : ℝ) ^ s * (n : ℝ) ^ (k - s) := by
    rw [← pow_add, Nat.add_sub_of_le hs]
  have hfac : (0 : ℝ) < (s.factorial : ℝ) := by positivity
  have hden : (0 : ℝ) < 2 ^ k * (k.factorial : ℝ) := by positivity
  have hns : (0 : ℝ) < (n : ℝ) ^ s := pow_pos hnR _
  have heq : ((s.factorial : ℝ) / (2 ^ k * (k.factorial : ℝ))) *
      (n : ℝ) ^ (k - s) =
      ((n : ℝ) ^ k / (2 ^ k * (k.factorial : ℝ))) /
        ((n : ℝ) ^ s / (s.factorial : ℝ)) := by
    rw [hpow]
    field_simp
  change ((s.factorial : ℝ) / (2 ^ k * (k.factorial : ℝ))) *
      (n : ℝ) ^ (k - s) ≤ (I : ℝ)
  rw [heq]
  apply (div_le_iff₀ (div_pos hns hfac)).2
  simpa only [mul_comm] using hbound

 

theorem stableSubset_image_poly_m {α : Type*} [DecidableEq α]
    (S : Finset α) (k m : ℕ) (Φ : Finset α → Finset α)
    (hk : 2 * k ≤ S.card) (hkpos : 0 < k) (hmk : m ≤ k)
    (hsub : ∀ A ∈ S.powersetCard k, Φ A ⊆ A)
    (hcard : ∀ A ∈ S.powersetCard k, m ≤ (Φ A).card) :
    (((k - m).factorial : ℝ) / (2 ^ k * (k.factorial : ℝ))) *
        (S.card : ℝ) ^ m ≤
      (((S.powersetCard k).image Φ).card : ℝ) := by
  simpa only [Nat.sub_sub_self hmk] using
    stableSubset_image_poly S k m Φ hk hkpos hmk hsub hcard


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.ChoicesCore
