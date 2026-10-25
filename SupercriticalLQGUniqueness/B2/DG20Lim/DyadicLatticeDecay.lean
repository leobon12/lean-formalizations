import SupercriticalLQGUniqueness.B2.DG20Lim.DyadicLatticeCoupledUnion
import Mathlib.Analysis.SpecialFunctions.Exp

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem dyadic_lattice_decay (K : ℕ) (hK : 12 ≤ K) :
    (4 : ℝ) ^ K * Real.exp (-(120 : ℝ) * (sparseDyadicIndices K).card) ≤
      Real.exp (-(K : ℝ)) := by
  have hcard := sparseDyadicIndices_card_lower hK
  have hreal : (5 : ℝ) * K ≤ 120 * (sparseDyadicIndices K).card := by
    exact_mod_cast (show 5 * K ≤ 120 * (sparseDyadicIndices K).card by omega)
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by
    have h := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hpow : (4 : ℝ) ^ K ≤ (Real.exp 4) ^ K := by gcongr
  have hexp : Real.exp (-(120 : ℝ) * (sparseDyadicIndices K).card) ≤
      Real.exp (-(5 : ℝ) * K) := Real.exp_monotone (by linarith)
  calc
    (4 : ℝ) ^ K * Real.exp (-(120 : ℝ) * (sparseDyadicIndices K).card) ≤
        (Real.exp 4) ^ K * Real.exp (-(5 : ℝ) * K) := by
          exact mul_le_mul hpow hexp (Real.exp_nonneg _) (pow_nonneg (Real.exp_nonneg _) _)
    _ = Real.exp (-(K : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem dyadic_lattice_probability_real_bound (R K : ℕ) (hK : 12 ≤ K)
    (c : ℝ) (hc : 0 ≤ c) :
    (dyadicLatticeBox R K).card *
      (c * Real.exp (-(120 : ℝ) * (sparseDyadicIndices K).card)) ≤
      ((32 * R + 1) ^ 2 : ℕ) * (c * Real.exp (-(K : ℝ))) := by
  have hbox := dyadicLatticeBox_card_le R K
  have hdecay := dyadic_lattice_decay K hK
  calc
    (dyadicLatticeBox R K).card *
        (c * Real.exp (-(120 : ℝ) * (sparseDyadicIndices K).card)) ≤
      ((32 * R + 1) ^ 2 * 4 ^ K : ℕ) *
        (c * Real.exp (-(120 : ℝ) * (sparseDyadicIndices K).card)) := by
          gcongr
    _ = ((32 * R + 1) ^ 2 : ℕ) *
        (c * ((4 : ℝ) ^ K *
          Real.exp (-(120 : ℝ) * (sparseDyadicIndices K).card))) := by
          push_cast
          ring
    _ ≤ ((32 * R + 1) ^ 2 : ℕ) *
        (c * Real.exp (-(K : ℝ))) := by gcongr

end SupercriticalLQGUniqueness.B2.DG20Lim
