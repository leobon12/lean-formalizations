import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaTrace

 









set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

structure BufferedMetricTrace (E : LSCMetric) (V : Set ℂ) where
  path : ℝ → ℂ
  start : ℝ
  stop : ℝ
  curve : E.IsCurve path start stop
  stays : ∀ t ∈ Icc start stop, path t ∈ V

namespace BufferedMetricTrace

def trace {E : LSCMetric} {V : Set ℂ} (P : BufferedMetricTrace E V) : Set V :=
  bufferedTrace P.path P.start P.stop P.stays

def cost {E : LSCMetric} {V : Set ℂ} (P : BufferedMetricTrace E V) : ℝ≥0∞ :=
  E.len P.path P.start P.stop

def first {E : LSCMetric} {V : Set ℂ} (P : BufferedMetricTrace E V) : V :=
  ⟨P.path P.start, P.stays P.start ⟨le_rfl, P.curve.1⟩⟩

def last {E : LSCMetric} {V : Set ℂ} (P : BufferedMetricTrace E V) : V :=
  ⟨P.path P.stop, P.stays P.stop ⟨P.curve.1, le_rfl⟩⟩

theorem first_mem_trace {E : LSCMetric} {V : Set ℂ}
    (P : BufferedMetricTrace E V) : P.first ∈ P.trace :=
  ⟨P.start, ⟨le_rfl, P.curve.1⟩, rfl⟩

theorem last_mem_trace {E : LSCMetric} {V : Set ℂ}
    (P : BufferedMetricTrace E V) : P.last ∈ P.trace :=
  ⟨P.stop, ⟨P.curve.1, le_rfl⟩, rfl⟩

theorem pair_cost {E : LSCMetric} {V : Set ℂ}
    (P : BufferedMetricTrace E V) {x y : V}
    (hx : x ∈ P.trace) (hy : y ∈ P.trace) :
    E.internal V (x, y) ≤ P.cost :=
  buffered_trace_pair_cost E P.curve P.stays hx hy

 

theorem chain_cost {E : LSCMetric} {V : Set ℂ}
    (P : BufferedMetricTrace E V) (rest : List (BufferedMetricTrace E V))
    (hcontact : (P :: rest).IsChain
      fun U W => (U.trace ∩ W.trace).Nonempty) :
    E.internal V (P.first, ((P :: rest).getLast (List.cons_ne_nil P rest)).last) ≤
      ((P :: rest).map BufferedMetricTrace.cost).sum := by
  let Q := (P :: rest).getLast (List.cons_ne_nil P rest)
  exact contact_chain_internal_bound E V
    (fun T : BufferedMetricTrace E V => T.trace)
    (fun T => T.cost)
    (fun T x y hx hy => T.pair_cost hx hy)
    P rest Q hcontact rfl P.first_mem_trace Q.last_mem_trace

end BufferedMetricTrace

end SupercriticalLQGUniqueness.B2.PfeAxioms
