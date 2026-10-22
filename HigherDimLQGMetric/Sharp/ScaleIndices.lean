import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Dyadic blocks inside the shell scale interval

For small `ε`, a consecutive block of dyadic radii lies in `[ε², ε]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

private theorem half_pow_antitone : Antitone (fun k : ℕ => (1 / 2 : ℝ) ^ k) := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij

/-- A dyadic scale just below `ε`, together with a block of scales in `[ε²,ε]`. -/
theorem exists_dyadic_block {ε : ℝ} (hε0 : 0 < ε) (hε8 : ε < 1 / 8) :
    ∃ k n : ℕ, n + 1 = k ∧ 0 < n ∧
      (1 / 2 : ℝ) ^ k < ε ∧ ε / 2 ≤ (1 / 2 : ℝ) ^ k ∧
      (∀ i < n, ε ^ 2 ≤ (1 / 2 : ℝ) ^ (k + i) ∧
        (1 / 2 : ℝ) ^ (k + i) ≤ ε) := by
  let q : ℝ := 1 / 2
  have hq0 : 0 < q := by dsimp [q]; norm_num
  have hq1 : q < 1 := by dsimp [q]; norm_num
  have hex : ∃ j : ℕ, q ^ j < ε := exists_pow_lt_of_lt_one hε0 hq1
  let k := Nat.find hex
  have hk : q ^ k < ε := Nat.find_spec hex
  have hk3 : 3 ≤ k := by
    by_contra hnot
    have hk2 : k ≤ 2 := by omega
    have hpow : q ^ 2 ≤ q ^ k := half_pow_antitone hk2
    have hq2 : q ^ 2 = (1 / 4 : ℝ) := by norm_num [q]
    rw [hq2] at hpow
    linarith
  have hprev : ε ≤ q ^ (k - 1) := by
    exact le_of_not_gt (Nat.find_min hex (by omega))
  have hksucc : k - 1 + 1 = k := by omega
  have hhalf : ε / 2 ≤ q ^ k := by
    rw [← hksucc, pow_succ]
    dsimp [q]
    linarith
  refine ⟨k, k - 1, by omega, by omega, hk, hhalf, ?_⟩
  intro i hi
  have hi2 : i ≤ k - 2 := by omega
  have hqi : q ^ (k - 2) ≤ q ^ i := half_pow_antitone hi2
  have hk2 : k - 2 + 2 = k := by omega
  have hq2 : q ^ 2 = (1 / 4 : ℝ) := by norm_num [q]
  have hfour : q ^ k = q ^ (k - 2) / 4 := by
    have h : q ^ (k - 2 + 2) = q ^ (k - 2) / 4 := by
      rw [pow_add, hq2]
      ring
    rwa [hk2] at h
  have hlow : ε ^ 2 ≤ q ^ (k + i) := by
    rw [pow_add]
    have hqi2 : 2 * ε ≤ q ^ i := by
      linarith
    calc
      ε ^ 2 = (ε / 2) * (2 * ε) := by ring
      _ ≤ q ^ k * q ^ i := mul_le_mul hhalf hqi2 (by positivity) (by positivity)
  have hup : q ^ (k + i) ≤ ε := by
    have hpow : q ^ (k + i) ≤ q ^ k := half_pow_antitone (Nat.le_add_right k i)
    exact hpow.trans hk.le
  exact ⟨hlow, hup⟩

end HigherDimLQGMetric
