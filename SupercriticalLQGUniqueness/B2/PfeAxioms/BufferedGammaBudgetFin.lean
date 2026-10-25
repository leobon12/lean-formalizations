import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaBudget

 








set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem finiteBridgeBudget_le_fin_sum {E : LSCMetric} {V : Set ℂ}
    (N : ℕ) (δ : ℝ≥0∞)
    (P : Fin (N + 1) → BufferedMetricTrace E V)
    (B : Fin (N + 1) → ℝ≥0∞)
    (hB : ∀ i, (P i).cost ≤ B i) :
    finiteBridgeBudget δ (P 0)
      (List.ofFn (fun i : Fin N => P i.succ)) ≤
        (∑ i : Fin (N + 1), B i) + N • δ := by
  rw [finiteBridgeBudget_eq_sum]
  have hlist : (P 0 :: List.ofFn (fun i : Fin N => P i.succ)) =
      List.ofFn P := by simp only [List.ofFn_succ]
  rw [hlist]
  simp only [List.map_ofFn, List.sum_ofFn, List.length_ofFn]
  exact add_le_add (Finset.sum_le_sum fun i _ => hB i) le_rfl

end SupercriticalLQGUniqueness.B2.PfeAxioms
