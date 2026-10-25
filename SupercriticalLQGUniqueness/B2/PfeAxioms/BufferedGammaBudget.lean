import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaSkeleton

 








set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem finiteBridgeBudget_eq_sum {E : LSCMetric} {V : Set ℂ}
    (δ : ℝ≥0∞) (P : BufferedMetricTrace E V)
    (rest : List (BufferedMetricTrace E V)) :
    finiteBridgeBudget δ P rest =
      ((P :: rest).map BufferedMetricTrace.cost).sum +
        rest.length • δ := by
  induction rest generalizing P with
  | nil => simp [finiteBridgeBudget]
  | cons Q tail ih =>
      simp only [finiteBridgeBudget, List.map_cons, List.sum_cons,
        List.length_cons, succ_nsmul, ih Q]
      ac_rfl

end SupercriticalLQGUniqueness.B2.PfeAxioms
