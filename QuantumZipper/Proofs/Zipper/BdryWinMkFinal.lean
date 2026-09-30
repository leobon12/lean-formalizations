import QuantumZipper.Proofs.Zipper.BdryWinMkHyp
import QuantumZipper.Proofs.Zipper.BdryWinMkReduce
import QuantumZipper.Proofs.Zipper.SWCoreWinR

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-W1 (F): SW's boundary window split with the normalization at a large circle

Source: S. Sheffield, M. Wang, arXiv:1605.06171, proof of Theorem 4.2, pp. 18–19. The boundary
constants are SW's `C(N)`, `C̲(N)` for the exponent `γ/√2` (the semicircle-average increments are
`√2` times a Brownian motion, Duplantier–Sheffield 2011 §6); both tend to `1`.

* `swBdryWindowSplitStmtR_holds`: `SWCore.SWBdryWindowSplitStmtR γ (swC (γ/√2)) (swC' (γ/√2))`.
* `bdryWindowStmt_holds`: `F1.BdryWindowStmt` via `SWCore.bdryWindowStmt_of_splitR`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Real
open scoped Topology NNReal ENNReal

namespace QuantumZipper.SWCore

open E6 F1 LQGDimension.ExistAsm

/-- **SWC-W1: SW's boundary window split (proof of Thm 4.2, pp. 18–19)** for the free field
normalized at a large circle. -/
theorem swBdryWindowSplitStmtR_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    SWBdryWindowSplitStmtR γ (swC (γ / √2)) (swC' (γ / √2)) := by
  intro Ω _ P _ X hX R hR h0 N hN φ hφc hφs hφ0 hsupp
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hSR : ∀ t ∈ tsupport φ, |t| + 1 ≤ (R : ℝ) := fun t ht => by
    have := hsupp ht
    rw [mem_Ioo] at this
    have : |t| < (R : ℝ) - 1 := abs_lt.2 ⟨this.1, this.2⟩
    linarith
  have hc1 : swC (γ / √2) N *
      (∫⁻ ω, mkF (γ / √2) N true (fun q : swWinSet N => swBM q ω) ∂stdP).toReal = 1 := by
    rw [mkF_swBM_true, swC]
    refine inv_mul_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨?_, swWinMean_ne_top _ N⟩)
    exact (lt_of_lt_of_le zero_lt_one (one_le_swWinMean _ N)).ne'
  have hc2 : swC' (γ / √2) N *
      (∫⁻ ω, mkF (γ / √2) N false (fun q : swWinSet N => swBM q ω) ∂stdP).toReal = 1 := by
    rw [mkF_swBM_false, swC']
    exact inv_mul_cancel₀ (ENNReal.toReal_ne_zero.2
      ⟨(swWinMeanInf_pos _ N).ne', swWinMeanInf_ne_top _ N⟩)
  have hD1 := bWinMarkovData hX hR1 h0 γ (swC (γ / √2) N)
    (inv_nonneg.2 ENNReal.toReal_nonneg) N true
    (by rw [mkF_swBM_true]; exact swWinMean_ne_top _ N) hc1 (mkF_true_sq_ne_top _ N) hSR
  have hD2 := bWinMarkovData hX hR1 h0 γ (swC' (γ / √2) N)
    (inv_nonneg.2 ENNReal.toReal_nonneg) N false
    (by rw [mkF_swBM_false]; exact swWinMeanInf_ne_top _ N) hc2 (mkF_false_sq_ne_top _ N) hSR
  have e1 : (fun x j u => bWin γ N true x j u) = fun x j u => bSupWin γ x N j u := by
    funext x j u; simp [bWin]
  have e2 : (fun x j u => bWin γ N false x j u) = fun x j u => bInfWin γ x N j u := by
    funext x j u; simp [bWin]
  rw [e1] at hD1
  rw [e2] at hD2
  exact ⟨bdryWinSplit_of_markovData hγ hγ2 hN hφc hφs hφ0 hD1,
    bdryWinSplit_of_markovData hγ hγ2 hN hφc hφs hφ0 hD2⟩

/-- **`F1.BdryWindowStmt`** from the boundary window split with SW's constants for `γ/√2`. -/
theorem bdryWindowStmt_holds : BdryWindowStmt :=
  bdryWindowStmt_of_splitR fun γ hγ hγ2 =>
    ⟨swC (γ / √2), swC' (γ / √2), tendsto_swC _, tendsto_swC' _,
      swBdryWindowSplitStmtR_holds hγ hγ2⟩

end QuantumZipper.SWCore
