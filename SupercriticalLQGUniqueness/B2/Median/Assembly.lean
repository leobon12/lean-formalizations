import SupercriticalLQGUniqueness.B2.Median.NoGap
import SupercriticalLQGUniqueness.B2.Median.Scale

 




set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

open Uniqueness.Toolkit.CompactPathInfimum

 

theorem crossingInf_eq_mul_of_dist_scale
    (D E : LSCMetric) (C : ℝ) (hC : 0 < C)
    (hscale : ∀ x y : ℂ, E (x, y) = ENNReal.ofReal C * D (x, y)) :
    crossingInf E = ENNReal.ofReal C * crossingInf D :=
  compactPathInf_eq_mul_of_dist_scale D E (ENNReal.ofReal C)
    (ENNReal.ofReal_pos.mpr hC).ne' ENNReal.ofReal_ne_top
    hscale unitSquare LQGMetric.leftSide LQGMetric.rightSide

 

theorem eq_one_of_proportional_crossing_medians
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D E : Ω → LSCMetric)
    (C : ℝ) (hC : 0 < C)
    (hprop : ∀ᵐ ω ∂P, ∀ x y : ℂ,
      E ω (x, y) = ENNReal.ofReal C * D ω (x, y))
    (hmedD : IsMedian P (fun ω => crossingInf (D ω)) 1)
    (hmedE : IsMedian P (fun ω => crossingInf (E ω)) 1)
    (hng : ∀ x y : ℝ≥0∞, x < y → y ≠ ∞ →
      0 < P {ω | crossingInf (D ω) ≤ x} →
      0 < P {ω | x < crossingInf (D ω) ∧ crossingInf (D ω) < y}) :
    C = 1 := by
  have hae : (fun ω => crossingInf (E ω)) =ᵐ[P]
      (fun ω => ENNReal.ofReal C * crossingInf (D ω)) := by
    filter_upwards [hprop] with ω hω
    exact crossingInf_eq_mul_of_dist_scale (D ω) (E ω) C hC (hω)
  have hmedScaled :=
    (Exponent.HeatVersion.isMedian_congr_ae P hae 1).mp hmedE
  exact eq_one_of_noGap_finite_and_scaled_medians P
    (fun ω => crossingInf (D ω)) hng C hC hmedD hmedScaled

end SupercriticalLQGUniqueness.B2.Median
