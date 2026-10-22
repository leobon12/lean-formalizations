import HigherDimLQGMetric.LfppTight.CoupledTight
import HigherDimLQGMetric.LfppTight.MetricLawMeas

/-! Identification of the continuous metric totalizations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_metricOfFieldC_eq_normMetricC {d : ℕ}
    (ξ a : ℝ) (φ : C(Rd d, ℝ)) :
    l6a_metricOfFieldC ξ a⁻¹ φ = DGZ.normMetricC ξ φ a := by
  apply ContinuousMap.ext
  intro p
  rw [l6a_metricOfFieldC, toCMapRd_apply_of_continuous
    ((continuous_fieldLfpp φ.continuous).const_smul a⁻¹),
    DGZ.normMetricC_apply φ.continuous]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [fieldLfpp_eq_lfppDistOn φ.continuous p]
  rfl

theorem l6a_ae_metricOfFieldC_eq_normMetricC {d : ℕ} (ξ a : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (H : Rd d → Ω → ℝ)
    (hc : ∀ᵐ ω ∂P, Continuous fun z => H z ω) :
    (fun ω => l6a_metricOfFieldC ξ a⁻¹
        (l6a_toFieldCMap (fun z => H z ω))) =ᵐ[P]
      (fun ω => DGZ.normMetricC ξ (fun z => H z ω) a) := by
  filter_upwards [hc] with ω hω
  rw [show l6a_toFieldCMap (fun z => H z ω) =
    (⟨fun z => H z ω, hω⟩ : C(Rd d, ℝ)) from dite_eq_left hω,
    l6a_metricOfFieldC_eq_normMetricC]
  rfl

end HigherDimLQGMetric
