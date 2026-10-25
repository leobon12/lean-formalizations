import SupercriticalLQGUniqueness.Frozen.TestTranslate

/-! Scratch freeze split of SLUField.lean:101. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun IsWholePlaneGFF IsGFFPlusCont bumpTest heatTrunc IsPiecewiseC1Path lfppLen leftSide rightSide)

namespace SupercriticalLQGUniqueness
open TopologicalSpace

/-- The translated field `h(· + z)` (DG l. 571): `⟨h(· + z), φ⟩ = ⟨h, φ(· - z)⟩`. -/
def translateDist (z : ℂ) (h : DistC) : DistC :=
  h.comp (testTranslate z)
end SupercriticalLQGUniqueness
