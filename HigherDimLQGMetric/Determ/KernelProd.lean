import HigherDimLQGMetric.Determ.ConstMeasure

/-! Simultaneous product laws for all ball radii and mesh sizes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem determ_kernel_prod {d : ℕ} [Nonempty (ContMetric d)]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {D : Ω → ContMetric d} {ξ : ℝ}
    (hh : IsNormalizedLGF h P) (hloc : IsXiAdditiveRd ξ P h D D) :
    ∀ᵐ g ∂P.map h, ∀ n j : ℕ, ∀ᵐ θ ∂(volume : Measure (Fin d → ℝ)),
      (condDistrib D h P g).map (determY (1 / ((j : ℝ) + 1)) θ
        (determFixedBox (d := d) (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1))) =
      Measure.pi fun k : determFixedBox (d := d) (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1) =>
        (condDistrib D h P g).map
          (determ_enc (determCube (1 / ((j : ℝ) + 1)) θ k)) := by
  have h := ae_all_iff.2 fun n : ℕ => ae_all_iff.2 fun j : ℕ =>
    determ_grid_condDistrib_pi_ae hh hloc (by positivity : 0 < 1 / ((j : ℝ) + 1))
      (determFixedBox (d := d) (1 / ((j : ℝ) + 1)) ((n : ℝ) + 1))
  filter_upwards [h] with g hg n j
  exact hg n j

end HigherDimLQGMetric
