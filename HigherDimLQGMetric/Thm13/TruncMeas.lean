import HigherDimLQGMetric.Trunc.LFPP
import HigherDimLQGMetric.LfppTight.LawTransfer
import HigherDimLQGMetric.Field.Measurable
import HigherDimLQGMetric.Select.MetricBorel
import HigherDimLQGMetric.Select.Internal

/-!
# Measurability of the everywhere defined truncated field

For a positive cutoff, the truncated convolution is a genuine test-function
pairing at each point. Its continuous modification is therefore a measurable
continuous map, and its LFPP distance is a measurable continuous-map-valued
functional. These are the input measurability facts for the global assignment
in [1, Theorem 1.3].
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The truncated convolution, bundled as a continuous field for every distribution. -/
def l8_truncFieldC (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : 0 < ε) (g : DistRd d) : C(Rd d, ℝ) :=
  ⟨truncMollify κ ε g, l2c_continuous_truncMollify hd hκ hε g⟩

theorem l8_measurable_truncFieldC (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) {ε : ℝ} (hε : 0 < ε) :
    Measurable (l8_truncFieldC hd hκ hε) := by
  apply ContinuousMap.measurable_iff_eval.2
  intro z
  exact measurable_distOn_apply (truncTest κ ε z)

/-- The continuous two-point LFPP function of the truncated field is Borel. -/
theorem l8_measurable_truncMetricC (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ a : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun g : DistRd d =>
      l6a_metricOfFieldC ξ a (l8_truncFieldC hd hκ hε g)) :=
  (l6a_measurable_metricOfFieldC ξ a).comp
    (l8_measurable_truncFieldC hd hκ hε)

/-- The unscaled LFPP metric is Borel as a `ContMetric`. -/
theorem l8_measurable_fieldLfppMetric (ξ : ℝ) :
    Measurable (fieldLfppMetric (d := d) ξ) := by
  have hm : Measurable (fun φ : C(Rd d, ℝ) => (fieldLfppMetric ξ φ).1) := by
    have heq : (fun φ : C(Rd d, ℝ) => (fieldLfppMetric ξ φ).1) =
        l6a_metricOfFieldC ξ 1 := by
      funext φ
      apply ContinuousMap.ext
      intro p
      rw [fieldLfppMetric_apply, l6a_metricOfFieldC,
        toCMapRd_apply_of_continuous ((continuous_fieldLfpp φ.continuous).const_smul 1)]
      simp only [Pi.smul_apply, one_smul]
    rw [heq]
    exact l6a_measurable_metricOfFieldC ξ 1
  apply Measurable.subtype_mk
  exact hm

/-- The truncated LFPP metric is a measurable continuous length metric. -/
theorem l8_measurable_truncContMetric (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    Measurable (fun g : DistRd d =>
      fieldLfppMetric ξ (l8_truncFieldC hd hκ hε g)) :=
  (l8_measurable_fieldLfppMetric ξ).comp
    (l8_measurable_truncFieldC hd hκ hε)

theorem l8_truncContMetric_isLength (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε) (g : DistRd d) :
    (fieldLfppMetric ξ (l8_truncFieldC hd hκ hε g)).IsLength :=
  fieldLfppMetric_isLength ξ _

/-- Every fixed internal distance of the truncated LFPP metric is Borel in the input
distribution. The domain can be any open set; in the patch it is a ball. -/
theorem l8_measurable_truncInternal (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε) {V : Set (Rd d)} (hV : IsOpen V)
    (z w : Rd d) :
    Measurable (fun g : DistRd d =>
      (fieldLfppMetric ξ (l8_truncFieldC hd hκ hε g)).internal V z w) := by
  have hm : Measurable (fun g : DistRd d =>
      (fieldLfppMetric ξ (l8_truncFieldC hd hκ hε g)).chainInf V z w) :=
    (ContMetric.measurable_chainInf V).comp
      ((l8_measurable_truncContMetric hd hκ ξ hε).prodMk
        (measurable_const.prodMk measurable_const))
  convert hm using 1
  funext g
  exact (ContMetric.internal_eq_chainInf _
    (l8_truncContMetric_isLength hd hκ ξ hε g) hV z w)

end HigherDimLQGMetric
