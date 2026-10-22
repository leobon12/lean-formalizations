import HigherDimLQGMetric.Determ.ESInt
import HigherDimLQGMetric.Metric.WeylBridge

/-! Pointwise metric comparison passes to the countable internal-distance formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem determ_chainInf_le_of_le {d : ℕ} {D E : ContMetric d}
    (hD : D.IsLength) {C : ℝ} (hC : 0 < C)
    (h : ∀ x y : Rd d, E.1 (x, y) ≤ C * D.1 (x, y))
    {U : Set (Rd d)} (hU : IsOpen U) (z w : Rd d) :
    E.chainInf U z w ≤ ENNReal.ofReal C * D.chainInf U z w := by
  rw [← D.internal_eq_chainInf hD hU]
  exact (E.chainInf_le_internal hU z w).trans
    (ContMetric.internal_le_mul_of_le (D := D) (E := E) hC h U z w)

theorem determ_chainInf_succ_le {d : ℕ} {D : ContMetric d}
    (hD : D.IsLength) (m : ℕ) (z w : Rd d) :
    determF (m + 1) z w D ≤ determF m z w D := by
  unfold determF
  rw [← D.internal_eq_chainInf hD Metric.isOpen_ball,
    ← D.internal_eq_chainInf hD Metric.isOpen_ball]
  exact LQGMetric.MetricGeometry.internalEDist_anti
    (Set.image_mono (Metric.ball_subset_ball (by push_cast; linarith))) _ _

end HigherDimLQGMetric
