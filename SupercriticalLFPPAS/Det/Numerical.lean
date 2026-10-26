import Mathlib

/-! Deterministic finite-sequence estimate used in the proof of Lemma 3.4. -/

set_option autoImplicit false
noncomputable section

namespace SupercriticalLFPPAS

/-- If successive tails contract by a fixed factor, the final term is controlled by the
initial tail. This is the numerical iteration in the proof of Lemma 3.4. -/
theorem d1_geometric_tail_bound {N : ℕ} {C L R : ℝ} {S y : ℕ → ℝ}
    (hC : 0 < C) (hR : 0 < R)
    (hbase : 2 * S 0 ≤ L)
    (hterminal : S N = y N)
    (hcontract : ∀ i < N, R * S (i + 1) ≤ S i) :
    C * y N ≤ (C / (2 * R ^ N)) * L := by
  have hiter : ∀ k ≤ N, R ^ k * S k ≤ S 0 := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hkN : k < N := by omega
        have hpow : 0 ≤ R ^ k := pow_nonneg hR.le k
        calc
          R ^ (k + 1) * S (k + 1) = R ^ k * (R * S (k + 1)) := by ring
          _ ≤ R ^ k * S k := mul_le_mul_of_nonneg_left (hcontract k hkN) hpow
          _ ≤ S 0 := ih (by omega)
  have htail : R ^ N * y N ≤ L / 2 := by
    rw [← hterminal]
    have := hiter N le_rfl
    nlinarith
  have hmul : C * (R ^ N * y N) ≤ C * (L / 2) := mul_le_mul_of_nonneg_left htail hC.le
  have hden : 2 * R ^ N ≠ 0 := by positivity
  have hgoal : C * y N * (2 * R ^ N) ≤ C * L := by
    nlinarith [hmul]
  calc
    C * y N = (C * y N * (2 * R ^ N)) / (2 * R ^ N) := by
      field_simp [hden]
    _ ≤ (C * L) / (2 * R ^ N) := (div_le_div_iff_of_pos_right (by positivity)).2 hgoal
    _ = (C / (2 * R ^ N)) * L := by ring

end SupercriticalLFPPAS
