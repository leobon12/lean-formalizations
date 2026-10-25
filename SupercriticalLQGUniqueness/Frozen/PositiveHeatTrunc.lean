import SupercriticalLQGUniqueness.Frozen.IsMedian

/-! Scratch freeze split of SLUField.lean:178. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness

/-- The truncated heat kernel `w ↦ p_s(z, w) χ_n(w)` (DG l. 284; `LQGMetric.heatTrunc`) on its
source carrier: positive times `s > 0` only. -/
def positiveHeatTrunc (s : Set.Ioi (0 : ℝ)) (z : ℂ) (n : ℕ) : TestC :=
  heatTrunc (s : ℝ) z n
end SupercriticalLQGUniqueness
