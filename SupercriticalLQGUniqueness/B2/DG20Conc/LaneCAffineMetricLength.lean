import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConjMetric
import LQGMetric.Metric.WeylScaling

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

theorem laneC_affineMetric_len (D : ContMetric) (r : ℝ) (hr : r ≠ 0)
    (z : ℂ) (ρ : ℝ → ℂ) (a b : ℝ) :
    (D.affine r hr z).len ρ a b =
      D.len (fun t => (r : ℂ) * ρ t + z) a b := by
  unfold ContMetric.len MetricGeometry.curveLength
  symm
  exact MetricGeometry.eVariationOn_comp_eq_of_edist_eq
    (X := (D.affine r hr z).Space) (Z := D.Space)
    (f := fun x => (LQGMetric.affinePt r z (x : ℂ) : D.Space))
    (P := ρ) (s := Set.Icc a b)
    (by intro x _ y _; rfl)

end SupercriticalLQGUniqueness.B2.DG20Conc
