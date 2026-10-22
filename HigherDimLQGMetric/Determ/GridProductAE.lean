import HigherDimLQGMetric.Determ.GridJoint

/-!
# Conditional product law for almost every grid translation

The fixed-translation result has a translation-dependent exceptional set of
fields. Joint measurability and Tonelli interchange the quantifiers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem determ_grid_condDistrib_pi_ae {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Nonempty (ContMetric d)]
    {h : Ω → DistRd d} {D : Ω → ContMetric d} {ξ : ℝ}
    (hh : IsNormalizedLGF h P) (hloc : IsXiAdditiveRd ξ P h D D)
    {ε : ℝ} (hε : 0 < ε) (S : Finset (Fin d → ℤ)) :
    ∀ᵐ g ∂P.map h, ∀ᵐ θ ∂(volume : Measure (Fin d → ℝ)),
      (condDistrib D h P g).map
          (fun D (i : S) => determ_enc (determCube ε θ i.1) D) =
        Measure.pi fun i : S =>
          (condDistrib D h P g).map (determ_enc (determCube ε θ i.1)) := by
  have hm := LQGMetric.LM.t17v_measurableSet_pi
    (Θ := Fin d → ℝ) (condDistrib D h P)
    (Y := fun p : (Fin d → ℝ) × ContMetric d =>
      fun i : S => determ_enc (determCube ε p.1 i.1) p.2)
    (determ_measurable_gridY ε S)
  exact (Measure.ae_ae_comm (μ := P.map h) (ν := (volume : Measure (Fin d → ℝ)))
    (p := fun g θ => (condDistrib D h P g).map
      (fun D (i : S) => determ_enc (determCube ε θ i.1) D) =
        Measure.pi fun i : S =>
          (condDistrib D h P g).map (determ_enc (determCube ε θ i.1))) hm).2
    (Eventually.of_forall fun θ => determ_grid_condDistrib_pi hh hloc hε θ S)

end HigherDimLQGMetric
