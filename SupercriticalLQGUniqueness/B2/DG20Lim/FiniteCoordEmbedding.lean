import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteJointCoords
import LQGMetric.Papers.GM.S3.AttainedP36Conf
import LQGMetric.Field.StandardBorelMetric

 





set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def pointCircle (q : ℚ × ℚ) : RatCircle := ⟨q.1, q.2, 0, le_rfl⟩

theorem pointCircle_toSet (q : ℚ × ℚ) :
    (pointCircle q).toSet = {LQGMetric.ratPt q} := by
  simp [pointCircle, RatCircle.toSet, RatCircle.center, LQGMetric.ratPt]

theorem finiteCircleCoords_point (D : LQGMetric.ContMetric) (q r : ℚ × ℚ) :
    finiteCircleCoords D (pointCircle q, pointCircle r) =
      ENNReal.ofReal (D.1 (LQGMetric.ratPt q, LQGMetric.ratPt r)) := by
  rw [finiteCircleCoords, pointCircle_toSet, pointCircle_toSet]
  rw [LQGMetric.GM.setDist_eq_iInf]
  simp only [iInf_singleton]

 

theorem finiteCircleCoords_injective : Function.Injective finiteCircleCoords := by
  intro D E h
  apply Subtype.ext
  have hden : DenseRange
      (Prod.map LQGMetric.ratPt LQGMetric.ratPt :
        (ℚ × ℚ) × (ℚ × ℚ) → ℂ × ℂ) :=
    LQGMetric.GM.denseRange_ratPt.prodMap LQGMetric.GM.denseRange_ratPt
  apply ContinuousMap.ext
  have hfun : (D.1 : ℂ × ℂ → ℝ) = (E.1 : ℂ × ℂ → ℝ) :=
    hden.equalizer D.1.continuous E.1.continuous (by
      funext q
      have heq := congrFun h (pointCircle q.1, pointCircle q.2)
      rw [finiteCircleCoords_point, finiteCircleCoords_point] at heq
      exact (ENNReal.ofReal_eq_ofReal_iff (LQGMetric.ContMetric.nonneg D _ _)
        (LQGMetric.ContMetric.nonneg E _ _)).mp heq)
  exact congrFun hfun

theorem measurableEmbedding_finiteCircleCoords :
    MeasurableEmbedding finiteCircleCoords :=
  measurable_finiteCircleCoords.measurableEmbedding finiteCircleCoords_injective

 

def circleCoordsInv : (RatCircle × RatCircle → ℝ≥0∞) → LQGMetric.ContMetric :=
  Function.extend finiteCircleCoords id fun _ => LQGMetric.euclidContMetric

theorem measurable_circleCoordsInv : Measurable circleCoordsInv :=
  measurableEmbedding_finiteCircleCoords.measurable_extend measurable_id measurable_const

@[simp] theorem circleCoordsInv_finiteCircleCoords (D : LQGMetric.ContMetric) :
    circleCoordsInv (finiteCircleCoords D) = D :=
  finiteCircleCoords_injective.extend_apply _ _ _

end SupercriticalLQGUniqueness.B2.DG20Lim
