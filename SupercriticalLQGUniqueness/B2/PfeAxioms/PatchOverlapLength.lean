import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 




theorem len_eq_of_internal_eq_on_patch
    (D E : LSCMetric) (U : Set ℂ)
    (hEq : D.internal U = E.internal U)
    (P : ℝ → U) (a b : ℝ)
    (hD : D.IsCurve (fun t => (P t : ℂ)) a b)
    (hE : E.IsCurve (fun t => (P t : ℂ)) a b) :
    D.len (fun t => (P t : ℂ)) a b =
      E.len (fun t => (P t : ℂ)) a b := by
  rw [Uniqueness.Toolkit.InternalMetrics.len_eq_internalLen D U P a b hD,
    Uniqueness.Toolkit.InternalMetrics.len_eq_internalLen E U P a b hE]
  unfold Uniqueness.Toolkit.InternalMetrics.internalLen
  simp only [hEq]

end SupercriticalLQGUniqueness.B2.PfeAxioms
