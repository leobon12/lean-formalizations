import SupercriticalLQGUniqueness.B2.PfeAxioms.RandomConstantOfStrongSB

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem euclideanControl_of_positive_scale
    (D E : LSCMetric) (a : ℝ) (ha : 0 < a)
    (hEq : ∀ p : ℂ × ℂ, E p = ENNReal.ofReal a * D p)
    (hControl : ∀ u : ℂ, ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, D (u, v) < ENNReal.ofReal η → dist u v < δ) :
    ∀ u : ℂ, ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ, E (u, v) < ENNReal.ofReal η → dist u v < δ := by
  intro u δ hδ
  obtain ⟨η, hη, hclose⟩ := hControl u δ hδ
  refine ⟨a * η, mul_pos ha hη, ?_⟩
  intro v hv
  have hlt : ENNReal.ofReal a * D (u, v) <
      ENNReal.ofReal a * ENNReal.ofReal η := by
    simpa only [hEq (u, v), ENNReal.ofReal_mul ha.le] using hv
  exact hclose v ((ENNReal.mul_lt_mul_iff_right
    (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top).mp hlt)

end SupercriticalLQGUniqueness.B2.PfeAxioms
