import SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusToSet

/-! Scratch freeze split of SLUMetric.lean:186. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace EuclideanAnnulus

/-- The inner boundary of `A` (DG l. 551): the circle of radius `r₁`. -/
def innerBoundary (A : EuclideanAnnulus) : Set ℂ :=
  Metric.sphere A.center A.innerRadius
end EuclideanAnnulus
end SupercriticalLQGUniqueness
