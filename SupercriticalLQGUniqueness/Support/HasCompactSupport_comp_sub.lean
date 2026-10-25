import SupercriticalLQGUniqueness.Support.Continuous_testTranslateK

 
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness
open TopologicalSpace

theorem hasCompactSupport_comp_sub (z : ℂ) {φ : ℂ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport fun x => φ (x - z) :=
  hφ.comp_homeomorph (Homeomorph.subRight z)
end SupercriticalLQGUniqueness
