import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling.CircleAverageConst
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.SampleV2
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3




 





set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
open LQGMetric (DistC)

theorem metric_addConst_eq_mul_of_regular
    (D : DistC → LSCMetric) (ξ : ℝ) (g : DistC)
    (hg : EndSaving.Choices.RegularAt D ξ g) (c : ℝ) (p : ℂ × ℂ) :
    D (LQGMetric.addConst g c) p =
      ENNReal.ofReal (Real.exp (ξ * c)) * D g p := by
  have hw := congrFun (hg.weyl (ContinuousMap.const ℂ c)) p
  change SupercriticalLQGUniqueness.weylScale ξ
      (ContinuousMap.const ℂ c) (D g) p =
    D (LQGMetric.addConst g c) p at hw
  exact hw.symm.trans
    (SupercriticalLQGUniqueness.weylScale_const ξ c (D g) hg.length p)

theorem internal_addConst_eq_mul_of_regular
    (D : DistC → LSCMetric) (ξ : ℝ) (g : DistC)
    (hg : EndSaving.Choices.RegularAt D ξ g) (c : ℝ)
    (U : Set ℂ) (p : U × U) :
    (D (LQGMetric.addConst g c)).internal U p =
      ENNReal.ofReal (Real.exp (ξ * c)) * (D g).internal U p := by
  have hk0 : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  exact Positivity.Witnesses.internal_eq_mul_of_dist_scale (D g)
    (D (LQGMetric.addConst g c)) _ hk0 ENNReal.ofReal_ne_top
    (fun x y => metric_addConst_eq_mul_of_regular D ξ g hg c (x, y)) U p

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Scaling
