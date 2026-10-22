import HigherDimLQGMetric.Locality.SecondMarkedLaw

/-! Exact measurable graphs pass through equality of joint laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

theorem l7a_ae_graph_of_equal_law
    {A B Ω E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableEq B] [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (Q : Measure E)
    (X : Ω → A) (Z : E → A)
    (hX : AEMeasurable X P) (hZ : Measurable Z)
    (hlaw : Q.map Z = P.map X)
    (f g : A → B) (hf : Measurable f) (hg : Measurable g)
    (heq : ∀ ω, f (X ω) = g (X ω)) :
    ∀ᵐ e ∂Q, f (Z e) = g (Z e) := by
  let S : Set A := {a | f a = g a}
  have hS : MeasurableSet S := measurableSet_eq_fun hf hg
  have hp : ∀ᵐ a ∂P.map X, a ∈ S :=
    (ae_map_iff hX hS).2 (Filter.Eventually.of_forall heq)
  have hq : ∀ᵐ a ∂Q.map Z, a ∈ S := by
    rw [hlaw]
    exact hp
  exact ae_of_ae_map hZ.aemeasurable hq

end HigherDimLQGMetric
