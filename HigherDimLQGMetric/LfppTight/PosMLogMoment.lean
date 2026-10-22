import HigherDimLQGMetric.LfppTight.MeanEnvelope

/-! Log moments and masses of nonnegative density measures. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_integral_logWeight_posM {d : ℕ} {f : Rd d → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (_hfw : Integrable (fun x : Rd d => Real.log (2 + ‖x‖) * f x)) :
    (∫ x : Rd d, Real.log (2 + ‖x‖) ∂(posM f)) =
      ∫ x : Rd d, Real.log (2 + ‖x‖) * f x := by
  rw [posM,
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    simp only [ENNReal.toReal_ofReal', smul_eq_mul, max_eq_left (hf0 x)]
    ring

theorem l6a_conv_mass_prob {d : ℕ}
    (μ ν : Measure (Rd d)) [IsProbabilityMeasure μ] [IsFiniteMeasure ν] :
    (Measure.conv μ ν).real univ = ν.real univ := by
  have hmass : (Measure.conv μ ν) univ = ν univ := by
    rw [Measure.conv, Measure.map_apply (by fun_prop) MeasurableSet.univ]
    rw [Set.preimage_univ, ← univ_prod_univ, Measure.prod_prod,
      measure_univ, one_mul]
  exact congrArg ENNReal.toReal hmass

end HigherDimLQGMetric
