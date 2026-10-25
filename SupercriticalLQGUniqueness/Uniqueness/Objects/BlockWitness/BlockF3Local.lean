import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness.BlockWitnessCode
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal




 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness

theorem goodSet_eq_of_internal_eq (D E : LSCMetric)
    (c u : ℂ) (s B : ℝ) (hu : u ∈ closedBall c s)
    (hEq : ∀ x : closedBall c s,
      D.internal (closedBall c s) (x, ⟨u, hu⟩) =
        E.internal (closedBall c s) (x, ⟨u, hu⟩)) :
    Objects.Producer.goodSet D c u s B hu = Objects.Producer.goodSet E c u s B hu := by
  ext x
  simp only [Objects.Producer.goodSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxs, hx, hcost⟩
    exact ⟨hxs, hx, by rw [← hEq ⟨x, hx⟩]; exact hcost⟩
  · rintro ⟨hxs, hx, hcost⟩
    exact ⟨hxs, hx, by rw [hEq ⟨x, hx⟩]; exact hcost⟩

theorem circleOuter_bad_eq_of_internal_eq (D E : LSCMetric)
    (c u : ℂ) (s B : ℝ) (hu : u ∈ closedBall c s)
    (hEq : ∀ x : closedBall c s,
      D.internal (closedBall c s) (x, ⟨u, hu⟩) =
        E.internal (closedBall c s) (x, ⟨u, hu⟩)) :
    Objects.Shadow.circleOuter c s.toNNReal 0
        (sphere c s \ Objects.Producer.goodSet D c u s B hu) =
      Objects.Shadow.circleOuter c s.toNNReal 0
        (sphere c s \ Objects.Producer.goodSet E c u s B hu) := by
  rw [goodSet_eq_of_internal_eq D E c u s B hu hEq]

 
theorem circleOuter_bad_eq_of_window_internal_eq (D E : LSCMetric)
    (U : Set ℂ) (c u : ℂ) (s B : ℝ)
    (hu : u ∈ closedBall c s)
    (hKU : closedBall c s ⊆ U)
    (hEq : D.internal U = E.internal U) :
    Objects.Shadow.circleOuter c s.toNNReal 0
        (sphere c s \ Objects.Producer.goodSet D c u s B hu) =
      Objects.Shadow.circleOuter c s.toNNReal 0
        (sphere c s \ Objects.Producer.goodSet E c u s B hu) := by
  apply circleOuter_bad_eq_of_internal_eq D E c u s B hu
  intro x
  exact congrFun (Toolkit.InternalMetrics.internal_eq_of_internal_eq D E hKU hEq)
    (x, ⟨u, hu⟩)


end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockWitness
