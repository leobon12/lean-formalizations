import HigherDimLQGMetric.Limits.StableAdjoin
import HigherDimLQGMetric.Sphere.Cont

/-!
# Stable convergence under a random scale factor

The sphere average is a measurable observable of the fixed field.  Adjoin it
to the metric law, then apply the continuous rescaling map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- The random scale transformation of a continuous metric is Borel. -/
theorem l6c_continuous_scaleMetric {d : ℕ} (ξ r : ℝ) :
    Continuous (fun q : ℝ × C(Rd d × Rd d, ℝ) =>
      Real.exp (-ξ * q.1) •
        q.2.comp ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul continuous_fst)).smul
      ((ContinuousMap.continuous_precomp _).comp continuous_snd)

/-- Stable convergence transfers to the randomly rescaled metric at one fixed radius. -/
theorem l6c_stable_scaleLaw {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hh : Measurable h)
    (X : ℕ → Ω → C(Rd d × Rd d, ℝ)) (Y : Ω → C(Rd d × Rd d, ℝ))
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hstable : StablyTendstoLU P h X Y) (ξ r : ℝ) :
    TendstoInDistribution
      (fun n ω => Real.exp (-ξ * sphereAvg (h ω) r 0) •
        (X n ω).comp ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩)
      atTop
      (fun ω => Real.exp (-ξ * sphereAvg (h ω) r 0) •
        (Y ω).comp ⟨fun p : Rd d × Rd d => (r • p.1, r • p.2), by fun_prop⟩)
      (fun _ => P) P := by
  have ha : Measurable (fun g : DistRd d => sphereAvg g r 0) :=
    measurable_sphereAvg_left r 0
  have hpair := l6c_stable_adjoin_scalar P h hh X Y hX hY hstable
    (fun g => sphereAvg g r 0) ha
  exact hpair.continuous_comp (l6c_continuous_scaleMetric ξ r)

end HigherDimLQGMetric
