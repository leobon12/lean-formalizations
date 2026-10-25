import SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusInnerBoundary

/-! Scratch freeze split of SLUMetric.lean:190. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace EuclideanAnnulus

/-- The outer boundary of `A` (DG l. 551): the circle of radius `r₂`. -/
def outerBoundary (A : EuclideanAnnulus) : Set ℂ :=
  Metric.sphere A.center A.outerRadius
end EuclideanAnnulus
end SupercriticalLQGUniqueness
