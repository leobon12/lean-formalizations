import SupercriticalConformalCovariance.TV.PointVariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric LQGMetric.GM QuantumZipper

namespace SupercriticalConformalCovariance.TV

/-- A jointly measurable continuous evaluation map for a distribution.
On a harmonic open set it agrees with the harmonic function. -/
def radialRepresentative (δ : ℝ) (hδ : 0 < δ) (T : DistC) : C(ℂ, ℝ) :=
  ⟨fun y => T (radBump δ hδ.le y) / ∫ x, radProf δ x,
   ((map_continuous T).comp (continuous_radBump δ hδ.le)).div_const _⟩

theorem radialRepresentative_apply (δ : ℝ) (hδ : 0 < δ) (T : DistC) (y : ℂ) :
    radialRepresentative δ hδ T y =
      T (radBump δ hδ.le y) / ∫ x, radProf δ x := rfl

theorem measurable_radialRepresentative (δ : ℝ) (hδ : 0 < δ) :
    Measurable (radialRepresentative δ hδ) :=
  ContinuousMap.measurable_iff_eval.2 fun y =>
    (measurable_distOn_apply (radBump δ hδ.le y)).div_const _

theorem radialRepresentative_eq_of_harmonic
    {V : TopologicalSpace.Opens ℂ} {g : ℂ → ℝ}
    (hg : InnerProductSpace.HarmonicOnNhd g V) {T : DistC}
    (hT : ∀ φ : TestOn V, restrictTo V T φ = ∫ x, g x * φ x)
    {δ : ℝ} (hδ : 0 < δ) {y : ℂ} (hy : closedBall y δ ⊆ V) :
    radialRepresentative δ hδ T y = g y := by
  rw [radialRepresentative_apply, pair_radBump_of_harmonic hg hT hδ hy]
  exact mul_div_cancel_right₀ (g y) (integral_radProf_pos hδ).ne'

theorem radialRepresentative_sub_zero (δ : ℝ) (hδ : 0 < δ)
    (T : DistC) (y : ℂ) :
    radialRepresentative δ hδ T y - radialRepresentative δ hδ T 0 =
      T (radDiff hδ.le y 0).1 / ∫ x, radProf δ x := by
  simp only [radialRepresentative_apply, radDiff, map_sub]
  ring

theorem closedBall_subset_ball_zero_of_norm_add_lt
    {L δ : ℝ} {y : ℂ} (hy : ‖y‖ + δ < L) :
    closedBall y δ ⊆ ball (0 : ℂ) L := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  rw [mem_ball, dist_zero_right]
  have ht := norm_add_le (x - y) y
  rw [sub_add_cancel] at ht
  linarith

end SupercriticalConformalCovariance.TV
