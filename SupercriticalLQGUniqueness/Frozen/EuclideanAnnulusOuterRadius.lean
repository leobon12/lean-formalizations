import SupercriticalLQGUniqueness.Frozen.EuclideanAnnulusInnerRadius

/-! Scratch freeze split of SLUMetric.lean:179. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace EuclideanAnnulus

/-- Outer radius of a valid Euclidean annulus. -/
def outerRadius (A : EuclideanAnnulus) : ℝ := A.1.2.2
end EuclideanAnnulus
end SupercriticalLQGUniqueness
