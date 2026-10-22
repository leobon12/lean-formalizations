import HigherDimLQGMetric.Locality.FiniteArray

/-! Tightness depends only on the coordinate laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

theorem l7a_tight_of_equal_laws
    {A Ω E : Type*} [TopologicalSpace A] [MeasurableSpace A]
    [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure E)
    (X : ℕ → Ω → A) (Y : ℕ → E → A)
    (heq : ∀ n, P.map (X n) = Q.map (Y n))
    (hY : IsTightMeasureSet {ν : Measure A | ∃ n, ν = Q.map (Y n)}) :
    IsTightMeasureSet {ν : Measure A | ∃ n, ν = P.map (X n)} := by
  apply hY.subset
  rintro ν ⟨n, rfl⟩
  exact ⟨n, heq n⟩

theorem l7a_map_eq_of_joint_law
    {A B Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) (Q : Measure E)
    (X : Ω → A) (Z : E → A)
    (hX : Measurable X) (hZ : Measurable Z)
    (hlaw : P.map X = Q.map Z) (f : A → B) (hf : Measurable f) :
    P.map (f ∘ X) = Q.map (f ∘ Z) := by
  rw [← Measure.map_map hf hX, ← Measure.map_map hf hZ, hlaw]

end HigherDimLQGMetric
