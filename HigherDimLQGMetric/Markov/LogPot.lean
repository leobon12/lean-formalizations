import HigherDimLQGMetric.Markov.Transfer
import GaussianLQG.Field.Realization.Potential
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Local integrability of the logarithmic kernel in every positive dimension

The general-dimensional Markov projection uses smooth potentials of compact test densities.
The kernel is locally integrable; convolution with a compact smooth density is then smooth.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

private theorem locallyIntegrable_invSqrt_norm {d : ℕ} (hd : 1 ≤ d) :
    LocallyIntegrable (fun x : Rd d => ‖x‖ ^ (-(1 / 2 : ℝ))) volume := by
  have hdim : 1 ≤ Module.finrank ℝ (Rd d) := by simpa using hd
  have hm : Measurable (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) := by
    apply measurable_of_measurable_on_compl_singleton 0
    exact Continuous.measurable (continuousOn_iff_continuous_domRestrict.mp
      (continuous_id.continuousOn.rpow_const (by
        intro r hr
        exact Or.inl hr)))
  apply locallyIntegrable_of_norm_le_rpow hdim (C := 1) (α := (1 / 2 : ℝ))
  · rw [show (Module.finrank ℝ (Rd d) : ℝ) = d by simp]
    exact (by norm_num : (1 / 2 : ℝ) < 1).trans_le (by exact_mod_cast hd)
  · exact ae_of_all _ fun x => by
      simp only [one_mul, Real.norm_eq_abs]
      exact le_of_eq (abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _))
  · exact (hm.comp measurable_norm).aestronglyMeasurable

/-- The logarithmic kernel on `ℝ^d` is locally integrable in every positive dimension. -/
theorem markov_locallyIntegrable_log_norm {d : ℕ} (hd : 1 ≤ d) :
    LocallyIntegrable (fun x : Rd d => Real.log ‖x‖) volume := by
  have hpow : LocallyIntegrable (fun x : Rd d => ‖x‖ ^ (-(1 / 2 : ℝ))) volume :=
    locallyIntegrable_invSqrt_norm hd
  have hnorm : LocallyIntegrable (fun x : Rd d => ‖x‖) volume :=
    continuous_norm.locallyIntegrable
  have hdom : LocallyIntegrable
      (fun x : Rd d => 2 * ‖x‖ ^ (-(1 / 2 : ℝ)) + ‖x‖) volume :=
    (hpow.smul (2 : ℝ)).add hnorm
  rw [locallyIntegrable_iff]
  intro K hK
  have hki := (locallyIntegrable_iff.mp hdom) K hK
  apply Integrable.mono' hki
  · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
      |>.mono_measure (Measure.restrict_le_self)
  · exact ae_restrict_of_ae (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      simpa [mul_comm] using GaussianLQG.Realization.abs_log_le_rpow_neg_add
        (norm_nonneg x) (show (0 : ℝ) < 1 / 2 by norm_num))

/-- The logarithmic potential of a smooth compact density. -/
def markovLogPot {d : ℕ} (ψ : TestRd d) (x : Rd d) : ℝ :=
  ∫ y, -Real.log ‖x - y‖ * ψ y

theorem markovLogPot_eq_convolution {d : ℕ} (ψ : TestRd d) :
    markovLogPot ψ = fun x =>
      -(MeasureTheory.convolution ψ (fun v : Rd d => Real.log ‖v‖)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) x := by
  funext x
  rw [markovLogPot, MeasureTheory.convolution_def, ← integral_neg]
  congr 1
  funext y
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, norm_sub_rev x y]
  ring

/-- The logarithmic potential of a test density is smooth. -/
theorem markov_contDiff_logPot {d : ℕ} (hd : 1 ≤ d) (ψ : TestRd d) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (markovLogPot ψ) := by
  rw [markovLogPot_eq_convolution]
  exact (ψ.hasCompactSupport.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ψ.contDiff
      (markov_locallyIntegrable_log_norm hd)).neg

end HigherDimLQGMetric
