import SupercriticalLQGUniqueness.Frozen.WeylScale
import LQGMetric.Statement.GFF
import LQGMetric.Statement.LFPP
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SLUMetricAPI

/-! Scratch freeze split of SLUField.lean:47. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness
open TopologicalSpace

/-- The compact set `K + z`. -/
def translateCompacts (z : ℂ) (K : Compacts ℂ) : Compacts ℂ :=
  K.map (fun y => y + z) (by fun_prop)
end SupercriticalLQGUniqueness
