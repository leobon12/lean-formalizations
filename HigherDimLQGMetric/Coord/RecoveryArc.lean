import HigherDimLQGMetric.Coord.RecoveryPath

/-! # Segments of an arc-length parametrized path -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

def arcSegment {X : Type*} [TopologicalSpace X]
    (P : ℝ → X) {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) : Path (P a) (P b) := by
  let φ : ℝ → ℝ := fun t => a + (b - a) * t
  have hφc : Continuous φ := by fun_prop
  have hφmap : MapsTo φ (Icc 0 1) (Icc a b) := by
    intro t ht
    dsimp [φ]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) ht.1,
      mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht.2)]
  have hcont : ContinuousOn (P ∘ φ) (Icc 0 1) :=
    hP.comp hφc.continuousOn hφmap
  exact Path.ofLine hcont (by simp [φ]) (by simp [φ])

theorem arcSegment_apply {X : Type*} [TopologicalSpace X]
    (P : ℝ → X) {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (t : I) :
    arcSegment P hab hP t = P (a + (b - a) * (t : ℝ)) := rfl

theorem arcSegment_extend_apply {X : Type*} [TopologicalSpace X]
    (P : ℝ → X) {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (arcSegment P hab hP).extend t = P (a + (b - a) * t) := by
  rw [Path.extend_apply _ ht]
  rfl

theorem arcSegment_mem {X : Type*} [TopologicalSpace X]
    (P : ℝ → X) {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) {S : Set X}
    (hS : ∀ t ∈ Icc a b, P t ∈ S) (t : I) :
    arcSegment P hab hP t ∈ S := by
  rw [arcSegment_apply]
  apply hS
  have ht0 := t.property.1
  have ht1 := t.property.2
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) ht0,
    mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht1)]

theorem coordinatePathLength_arcSegment {X : Type*} [TopologicalSpace X]
    (δ : X → X → ℝ≥0∞) (P : ℝ → X)
    {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) :
    coordinatePathLength δ (arcSegment P hab hP) = curveLengthWith δ P a b := by
  unfold coordinatePathLength
  rw [curveLengthWith_congr_path
    (Q := P ∘ fun t => a + (b - a) * t)
    (fun t ht => arcSegment_extend_apply P hab hP ht)]
  rw [curveLengthWith_comp_monotoneOn δ P zero_le_one (by fun_prop)
    (fun s _ t _ hst => by gcongr)]
  simp

theorem coordinatePathWeightedLength_arcSegment {X : Type*} [TopologicalSpace X]
    (δ : X → X → ℝ≥0∞) (w : X → ℝ) (P : ℝ → X)
    {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) :
    coordinatePathWeightedLength δ w (arcSegment P hab hP) =
      weightedLengthWith δ w P a b := by
  unfold coordinatePathWeightedLength
  rw [weightedLengthWith_congr_path
    (Q := P ∘ fun t => a + (b - a) * t)
    (fun t ht => arcSegment_extend_apply P hab hP ht)]
  rw [weightedLengthWith_comp_monotoneOn δ w P zero_le_one (by fun_prop)
    (fun s _ t _ hst => by gcongr)]
  simp

end HigherDimLQGMetric
