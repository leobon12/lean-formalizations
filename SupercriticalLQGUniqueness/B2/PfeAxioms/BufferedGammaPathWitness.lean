import SupercriticalLQGUniqueness.B2.PfeAxioms.BufferedGammaFiniteEventual
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.EA1

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem eventually_buffered_curves_below
    {G : ℕ → LSCMetric} {V : Set ℂ}
    (x y : ℕ → V) {d B : ℝ≥0∞}
    (hxy : Tendsto (fun n => (G n).internal V (x n, y n)) atTop (𝓝 d))
    (hdB : d < B) :
    ∀ᶠ n in atTop, ∃ P : BufferedMetricTrace (G n) V,
      P.first = x n ∧ P.last = y n ∧ P.cost < B := by
  have hlt : ∀ᶠ n in atTop, (G n).internal V (x n, y n) < B :=
    hxy.eventually (isOpen_Iio.mem_nhds hdB)
  filter_upwards [hlt] with n hn
  obtain ⟨Q, a, b, hQ, hQV, hQa, hQb, hlen⟩ :=
    Uniqueness.Objects.Producer.exists_curve_of_internal_lt
      (G n) (x n).property (y n).property hn
  let P : BufferedMetricTrace (G n) V := ⟨Q, a, b, hQ, hQV⟩
  refine ⟨P, ?_, ?_, hlen⟩
  · exact Subtype.ext hQa
  · exact Subtype.ext hQb

end SupercriticalLQGUniqueness.B2.PfeAxioms
