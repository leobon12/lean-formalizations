import SupercriticalLQGUniqueness.Frozen.PositiveHeatTrunc

/-! Scratch freeze split of SLUField.lean:182. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- The closed unit square `[0,1]²`. -/
def unitSquare : Set ℂ :=
  {z | 0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1}
end SupercriticalLQGUniqueness
