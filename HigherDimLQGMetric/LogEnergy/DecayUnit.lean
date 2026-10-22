import HigherDimLQGMetric.LogEnergy.DecayCov
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem logCovRd_decay_unit {d : ℕ} (hd : 1 ≤ d) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε ∈ Set.Icc (0:ℝ) (a/(8*b)), 0 < ε →
      ∀ φ ψ : TestRd0 d,
        tsupport φ.1 ⊆ ann 0 a b →
        tsupport ψ.1 ⊆ Metric.closedBall 0 b →
        |logCovRd φ.1 (testAffinePull ε 0 ψ.1)| ≤
          ((C*ε)*ε^d)*(logNorm φ.1*logNorm ψ.1) := by
  obtain ⟨C,hC,hCM⟩ := decayKernelPotential_isCMBounded hd ha hab
  refine ⟨C,hC,?_⟩
  intro ε hε hεpos φ ψ hφ hψ
  rw [logCovRd_affineInner_eq_potential ha hab hεpos φ ψ hφ hψ]
  rw [abs_mul, abs_of_nonneg (pow_nonneg hε.1 _)]
  have h := hCM ε hε ψ φ
  have heq : (∫ x : Rd d, φ.1 x * decayKernelPotential ha (ha.trans hab) ε ψ.1 x) =
      ∫ x : Rd d, decayKernelPotential ha (ha.trans hab) ε ψ.1 x * φ.1 x := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => mul_comm _ _
  rw [heq]
  calc
    ε^d * |∫ x : Rd d, decayKernelPotential ha (ha.trans hab) ε ψ.1 x * φ.1 x| ≤
      ε^d * (((C*ε)*logNorm ψ.1)*logNorm φ.1) :=
        mul_le_mul_of_nonneg_left h (pow_nonneg hε.1 _)
    _ = ((C*ε)*ε^d)*(logNorm φ.1*logNorm ψ.1) := by ring
end HigherDimLQGMetric
