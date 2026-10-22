import HigherDimLQGMetric.Collapse.CurveCompact

/-! # Competitors below a strict weighted distance bound -/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- Unfold the infimum defining the confined weighted distance at a strict upper bound. -/
theorem exists_weighted_competitor {X : Type*} [MetricSpace X]
    {w : X → ℝ} {Y : Set X} {x y : X} {B : ℝ≥0∞}
    (h : weylDistOn w Y x y < B) :
    ∃ P : ℝ → X, ContinuousOn P (Icc 0 1) ∧ P 0 = x ∧ P 1 = y ∧
      MapsTo P (Icc 0 1) Y ∧ weightedLength w P 0 1 < B := by
  unfold weylDistOn at h
  obtain ⟨P, hP⟩ := iInf_lt_iff.mp h
  obtain ⟨hc, hP⟩ := iInf_lt_iff.mp hP
  obtain ⟨h0, hP⟩ := iInf_lt_iff.mp hP
  obtain ⟨h1, hP⟩ := iInf_lt_iff.mp hP
  obtain ⟨hY, hP⟩ := iInf_lt_iff.mp hP
  exact ⟨P, hc, h0, h1, hY, hP⟩

end HigherDimLQGMetric
