import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaBridge

 









set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

open BufferedMetricTrace

def finiteBridgeBudget {E : LSCMetric} {V : Set ℂ}
    (δ : ℝ≥0∞) (P : BufferedMetricTrace E V)
    (rest : List (BufferedMetricTrace E V)) : ℝ≥0∞ :=
  match rest with
  | [] => P.cost
  | Q :: tail => P.cost + δ + finiteBridgeBudget δ Q tail

 



theorem finite_buffered_bridge_bound {E : LSCMetric} {V : Set ℂ}
    (δ : ℝ≥0∞) (P : BufferedMetricTrace E V)
    (rest : List (BufferedMetricTrace E V))
    (hbridge : (P :: rest).IsChain fun U W =>
      ∃ R : BufferedMetricTrace E V,
        (U.trace ∩ R.trace).Nonempty ∧
        (R.trace ∩ W.trace).Nonempty ∧ R.cost ≤ δ)
    {x y : V} (hx : x ∈ P.trace)
    (hy : y ∈ ((P :: rest).getLast (List.cons_ne_nil P rest)).trace) :
    E.internal V (x, y) ≤ finiteBridgeBudget δ P rest := by
  induction rest generalizing P x with
  | nil =>
      simpa only [finiteBridgeBudget, List.getLast_singleton] using
        (P.pair_cost hx hy)
  | cons Q tail ih =>
      obtain ⟨hPQ, htail⟩ := (List.isChain_cons_cons.mp hbridge)
      obtain ⟨R, hPR, hRQ, hRcost⟩ := hPQ
      obtain ⟨u, hPu, hRu⟩ := hPR
      obtain ⟨v, hRv, hQv⟩ := hRQ
      have hy' : y ∈ ((Q :: tail).getLast (List.cons_ne_nil Q tail)).trace := by
        simpa using hy
      have htailBound : E.internal V (v, y) ≤ finiteBridgeBudget δ Q tail :=
        ih Q htail hQv hy'
      calc
        E.internal V (x, y) ≤
            E.internal V (x, u) + E.internal V (u, v) +
              E.internal V (v, y) := by
          have htri := E.isExtMetric_internal V
          calc
            _ ≤ E.internal V (x, u) + E.internal V (u, y) :=
              htri.2.2.2 x u y
            _ ≤ E.internal V (x, u) +
                (E.internal V (u, v) + E.internal V (v, y)) := by
              gcongr
              exact htri.2.2.2 u v y
            _ = _ := by ac_rfl
        _ ≤ P.cost + δ + finiteBridgeBudget δ Q tail := by
          exact add_le_add (add_le_add (P.pair_cost hx hPu)
            ((R.pair_cost hRu hRv).trans hRcost)) htailBound
        _ = finiteBridgeBudget δ P (Q :: tail) := rfl

end SupercriticalLQGUniqueness.B2.PfeAxioms
