import SupercriticalLQGUniqueness.Frozen.LSCMetricSpace

/-! Scratch freeze split of SLUMetric.lean:126. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- The identity map from `ℂ` to `(α, D)`. -/
def pt (D : LSCMetric) : ℂ → D.Space := id
end LSCMetric
end SupercriticalLQGUniqueness
