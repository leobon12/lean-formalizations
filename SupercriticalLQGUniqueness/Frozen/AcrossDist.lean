import SupercriticalLQGUniqueness.Frozen.Disconnects

/-! Scratch freeze split of SLUMetric.lean:207. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- DG Definition 1.11 (l. 555): `D (across A)`, the `D`-distance between the inner and outer
boundaries of the Euclidean annulus `A`. -/
def acrossDist (D : LSCMetric) (A : EuclideanAnnulus) : ℝ≥0∞ :=
  ⨅ (x ∈ A.innerBoundary) (y ∈ A.outerBoundary), D (x, y)
end SupercriticalLQGUniqueness
