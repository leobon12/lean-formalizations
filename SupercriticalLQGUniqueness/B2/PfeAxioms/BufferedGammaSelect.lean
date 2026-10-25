import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaBudgetFin

 









set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

def constantBufferedTrace (E : LSCMetric) {V : Set ℂ} (x : V) :
    BufferedMetricTrace E V where
  path := fun _ => x
  start := 0
  stop := 0
  curve := ⟨le_rfl, continuousOn_const⟩
  stays := fun _ _ => x.property

theorem select_eventual_segment_curves
    {G : ℕ → LSCMetric} {V : Set ℂ} (N : ℕ)
    (x y : Fin (N + 1) → ℕ → V)
    (B : Fin (N + 1) → ℝ≥0∞)
    (hgood : ∀ i, ∀ᶠ n in atTop,
      ∃ P : BufferedMetricTrace (G n) V,
        P.first = x i n ∧ P.last = y i n ∧ P.cost < B i) :
    ∃ P : (n : ℕ) → Fin (N + 1) → BufferedMetricTrace (G n) V,
      ∀ i, ∀ᶠ n in atTop,
        (P n i).first = x i n ∧
        (P n i).last = y i n ∧ (P n i).cost < B i := by
  classical
  let Good (n : ℕ) (i : Fin (N + 1)) : Prop :=
    ∃ P : BufferedMetricTrace (G n) V,
      P.first = x i n ∧ P.last = y i n ∧ P.cost < B i
  let P (n : ℕ) (i : Fin (N + 1)) : BufferedMetricTrace (G n) V :=
    if h : Good n i then Classical.choose h
    else constantBufferedTrace (G n) (x i n)
  refine ⟨P, ?_⟩
  intro i
  filter_upwards [hgood i] with n hn
  have hn' : Good n i := hn
  have hspec := Classical.choose_spec hn'
  simpa only [P, dite_eq_left hn'] using hspec

end SupercriticalLQGUniqueness.B2.PfeAxioms
