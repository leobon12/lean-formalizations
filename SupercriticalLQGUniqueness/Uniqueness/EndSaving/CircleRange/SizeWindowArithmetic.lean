import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith




 



set_option autoImplicit false
noncomputable section
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.CircleRange

 

theorem normalized_size_window
    {ε t ξ Q Δ : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (ht : 0 < t)
    (htlow : ε ^ 2 ≤ t) (htup : t ≤ ε)
    (hξ : 0 < ξ) (hQ : 0 < Q)
    (hΔ : |Δ| ≤ 3 * Real.log t⁻¹) :
    ε ^ (2 * ξ * (Q + 3)) ≤ t ^ (ξ * Q) * Real.exp (ξ * Δ) ∧
      t ^ (ξ * Q) * Real.exp (ξ * Δ) ≤
        ε ^ (ξ * min (Q - 3) (2 * (Q - 3))) := by
  have hloglow : 2 * Real.log ε ≤ Real.log t := by
    have h := Real.log_le_log (pow_pos hε 2) htlow
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hlogup : Real.log t ≤ Real.log ε := Real.log_le_log ht htup
  have hΔ' : 3 * Real.log t ≤ Δ ∧ Δ ≤ -(3 * Real.log t) := by
    rw [Real.log_inv] at hΔ
    rcases abs_le.mp hΔ with ⟨hl, hu⟩
    constructor <;> linarith only [hl, hu]
  have ha : 0 < ξ * (Q + 3) := mul_pos hξ (by linarith)
  have hlowLog : (2 * ξ * (Q + 3)) * Real.log ε ≤
      (ξ * Q) * Real.log t + ξ * Δ := by
    have h₁ := mul_le_mul_of_nonneg_left hloglow ha.le
    have h₂ := mul_le_mul_of_nonneg_left hΔ'.1 hξ.le
    nlinarith only [h₁, h₂]
  have huppLog : (ξ * Q) * Real.log t + ξ * Δ ≤
      (ξ * min (Q - 3) (2 * (Q - 3))) * Real.log ε := by
    have h₂ := mul_le_mul_of_nonneg_left hΔ'.2 hξ.le
    by_cases hQ3 : 3 ≤ Q
    · have hmin : min (Q - 3) (2 * (Q - 3)) = Q - 3 :=
        min_eq_left (by linarith)
      rw [hmin]
      have ha' : 0 ≤ ξ * (Q - 3) := mul_nonneg hξ.le (by linarith)
      have h₁ := mul_le_mul_of_nonneg_left hlogup ha'
      nlinarith only [h₁, h₂]
    · have hmin : min (Q - 3) (2 * (Q - 3)) = 2 * (Q - 3) :=
        min_eq_right (by linarith)
      rw [hmin]
      have ha' : ξ * (Q - 3) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hξ.le (by linarith)
      have h₁ := mul_le_mul_of_nonpos_left hloglow ha'
      nlinarith only [h₁, h₂]
  have hS : t ^ (ξ * Q) * Real.exp (ξ * Δ) =
      Real.exp ((ξ * Q) * Real.log t + ξ * Δ) := by
    rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
    congr 1
    ring
  rw [hS, Real.rpow_def_of_pos hε, Real.rpow_def_of_pos hε]
  constructor
  · apply Real.exp_le_exp.mpr
    nlinarith only [hlowLog]
  · apply Real.exp_le_exp.mpr
    nlinarith only [huppLog]

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.CircleRange
