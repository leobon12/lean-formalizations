import SupercriticalLQGUniqueness.Frozen.LSCMetricIsCurve

/-! Scratch freeze split of SLUMetric.lean:144. -/
set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace LSCMetric

/-- DG l. 415–419: the `D`-length of `P` on `[a, b]`, i.e. the supremum over partitions
`a = t₀ < ⋯ < t_n = b` of `∑ D (P t_{i-1}, P t_i)` (mathlib's `eVariationOn`; equality with the
partition supremum is `len_eq_partitionLengthSup`). -/
def len (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) : ℝ≥0∞ :=
  eVariationOn (D.pt ∘ P) (Icc a b)
end LSCMetric
end SupercriticalLQGUniqueness
