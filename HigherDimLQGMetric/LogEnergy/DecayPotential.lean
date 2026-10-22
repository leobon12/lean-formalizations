import HigherDimLQGMetric.LogEnergy.DecayCM
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem decayKernelPotential_deriv_bound {d : ℕ} (hd : 1 ≤ d)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)),
      ∀ (ψ : TestRd0 d) (x : Rd d),
        ‖iteratedFDeriv ℝ n
          (decayKernelPotential ha (ha.trans hab) ε ψ.1) x‖ ≤
          (C*ε)*logNorm ψ.1 := by
  obtain ⟨C,hC,hCM⟩ := decayKernelXDeriv_isCMBounded hd ha hab n
  refine ⟨C,hC,?_⟩
  intro ε hε ψ x
  rw [decayKernelPotential_iteratedFDeriv ha hab hε ψ.1 n x]
  apply ContinuousMultilinearMap.opNorm_le_bound
    (mul_nonneg (mul_nonneg hC.le hε.1) (logNorm_nonneg ψ.1))
  intro v
  let L : (Rd d [×n]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Rd d) ℝ v
  have hL : ‖L‖ ≤ ∏ i, ‖v i‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    simpa [L, mul_comm] using f.le_opNorm v
  have hCMv := hCM ε hε x L ψ
  have hint := decayKernelXDerivWeighted_integrable ha hab hε ψ.1 n x
  have heq : (decayKernelMoment ha (ha.trans hab) ε ψ.1 n x) v =
      ∫ u : Rd d, (L (decayKernelXDeriv ha (ha.trans hab) ε n (x,u))) * ψ.1 u := by
    rw [decayKernelMoment, ContinuousMultilinearMap.integral_apply hint v]
    apply integral_congr_ae
    exact ae_of_all _ fun u => by
      simp [decayKernelXDerivWeighted, L, smul_eq_mul, mul_comm]
  rw [heq, Real.norm_eq_abs]
  calc
    |∫ u : Rd d, L (decayKernelXDeriv ha (ha.trans hab) ε n (x,u)) * ψ.1 u| ≤
      ((C*ε)*‖L‖)*logNorm ψ.1 := hCMv
    _ ≤ ((C*ε)*logNorm ψ.1)*∏ i, ‖v i‖ := by
      have hnonneg : 0 ≤ (C*ε)*logNorm ψ.1 :=
        mul_nonneg (mul_nonneg hC.le hε.1) (logNorm_nonneg ψ.1)
      nlinarith [mul_le_mul_of_nonneg_left hL hnonneg]
end HigherDimLQGMetric
