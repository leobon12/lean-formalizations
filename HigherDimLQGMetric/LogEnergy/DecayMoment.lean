import HigherDimLQGMetric.LogEnergy.DecayParam
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

def decayKernelPotential {d : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ε : ℝ) (ψ : TestRd d) (x : Rd d) : ℝ :=
  ∫ u : Rd d, decayLocalKernelSpatial ha hb ε (x,u) * ψ u

theorem decayKernelPotential_iteratedFDeriv {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (ψ : TestRd d) (n : ℕ) (x : Rd d) :
    iteratedFDeriv ℝ n (decayKernelPotential ha (ha.trans hab) ε ψ) x =
      decayKernelMoment ha (ha.trans hab) ε ψ n x := by
  induction n generalizing x with
  | zero =>
      ext v
      change decayKernelPotential ha (ha.trans hab) ε ψ x = _
      rw [decayKernelMoment, ContinuousMultilinearMap.integral_apply
        (decayKernelXDerivWeighted_integrable ha hab hε ψ 0 x) v]
      apply integral_congr_ae
      exact ae_of_all _ fun u => by
        simp [decayKernelXDerivWeighted, decayKernelXDeriv,
          iteratedFDeriv_zero_apply, smul_eq_mul, mul_comm]
  | succ n ih =>
      rw [iteratedFDeriv_succ_eq_comp_left]
      change (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n+1) => Rd d) ℝ).symm
          (fderiv ℝ (iteratedFDeriv ℝ n
            (decayKernelPotential ha (ha.trans hab) ε ψ)) x) = _
      have heq : iteratedFDeriv ℝ n (decayKernelPotential ha (ha.trans hab) ε ψ) =
          decayKernelMoment ha (ha.trans hab) ε ψ n := by
        funext y
        exact ih y
      rw [heq]
      rw [(decayKernelMoment_hasFDerivAt ha hab hε ψ n x).fderiv]
      exact (LinearIsometryEquiv.symm_apply_apply _ _)

theorem decayKernelPotential_contDiff {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {ε : ℝ}
    (hε : ε ∈ Set.Icc (0:ℝ) (a/(8*b))) (ψ : TestRd d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (decayKernelPotential ha (ha.trans hab) ε ψ) := by
  apply contDiff_of_differentiable_iteratedFDeriv
  intro n _
  have heq : iteratedFDeriv ℝ n (decayKernelPotential ha (ha.trans hab) ε ψ) =
      decayKernelMoment ha (ha.trans hab) ε ψ n := by
    funext x
    exact decayKernelPotential_iteratedFDeriv ha hab hε ψ n x
  rw [heq]
  exact fun x => (decayKernelMoment_hasFDerivAt ha hab hε ψ n x).differentiableAt
end HigherDimLQGMetric
