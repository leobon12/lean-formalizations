import HigherDimLQGMetric.LfppTight.VarianceApproxBound
import HigherDimLQGMetric.LfppTight.SphereMeanGaussian
import HigherDimLQGMetric.LfppTight.SphereMeanTail

/-! The centered Gaussian sphere means have uniformly bounded variance at small cutoffs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_uniform_sphereMean_variance {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      Var[fun ω => l6a_convSphereMean κ ε (h ω); P] ≤ C := by
  obtain ⟨C, hC0, hC⟩ := l6a_uniform_meanTrunc_logCov hd hκ
  refine ⟨C, hC0, ?_⟩
  intro ε hε
  have hlim := (l6a_gaussianClosure_sphereMean hd κ hκ P h hh hε.1).2.2
  have hbound (n : ℕ) :
      Var[(fun ω => h ω (l6a_meanCenteredTest hd hκ hε.1 n).1); P] ≤ C := by
    have hcov := hC ε ⟨hε.1, hε.2.le⟩ n
    change |logCovRd (l6a_meanCenteredTest hd hκ hε.1 n).1
      (l6a_meanCenteredTest hd hκ hε.1 n).1| ≤ C at hcov
    have hvar : Var[(fun ω => h ω (l6a_meanCenteredTest hd hκ hε.1 n).1); P] =
        logCovRd (l6a_meanCenteredTest hd hκ hε.1 n).1
          (l6a_meanCenteredTest hd hκ hε.1 n).1 := by
      rw [← hh.1.covariance_eq, covariance_self
        (hh.1.gaussian.hasGaussianLaw_eval
          (l6a_meanCenteredTest hd hκ hε.1 n)).aemeasurable]
    rw [hvar]
    exact (le_abs_self _).trans hcov
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)

theorem l6a_uniform_sphereMean_tail {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) :
    ∃ L : ℝ, 0 < L ∧ ∀ ε ∈ Ioo (0 : ℝ) 1,
      P {ω | L < |l6a_convSphereMean κ ε (h ω)|} ≤ (8⁻¹ : ℝ≥0∞) := by
  obtain ⟨C, hC0, hC⟩ := l6a_uniform_sphereMean_variance hd κ hκ P h hh
  obtain ⟨L, hL, htail⟩ := l6a_uniform_sphereMean_tail_of_variance
    hd κ hκ P h hh hC0 hC (by norm_num : (0 : ℝ) < 1 / 8)
  refine ⟨L, hL, ?_⟩
  intro ε hε
  convert htail ε hε using 1
  rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8)]
  norm_num

end HigherDimLQGMetric
