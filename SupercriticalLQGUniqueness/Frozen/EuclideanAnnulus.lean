import SupercriticalLQGUniqueness.Frozen.LSCMetricInternal

/-! Scratch freeze split of SLUMetric.lean:167. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness

/-- A Euclidean annulus `𝔸_{r₁,r₂}(c)` with `0 < r₁ < r₂ < ∞` (DG l. 978–980, 573). -/
def EuclideanAnnulus : Type :=
  {t : ℂ × (ℝ × ℝ) // 0 < t.2.1 ∧ t.2.1 < t.2.2}
end SupercriticalLQGUniqueness
