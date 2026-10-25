import SupercriticalLQGUniqueness.B2.DG20Lim.CoordSpace
import LQGMetric.Papers.GM.S3.GoodAnnulusMeas4a

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
def finiteCircleCoords (D : LQGMetric.ContMetric) :
    RatCircle × RatCircle → ℝ≥0∞ :=
  fun q => LQGMetric.Blueprint.setDist D q.1.toSet q.2.toSet

 
theorem measurable_finiteCircleCoords : Measurable finiteCircleCoords := by
  apply measurable_pi_iff.2
  intro q
  exact LQGMetric.GM.measurable_setDist q.1.toSet q.2.toSet

end SupercriticalLQGUniqueness.B2.DG20Lim
