import SupercriticalConformalCovariance.Rotation.Local
import SupercriticalLQGUniqueness.Frozen.StrongLQGMetric_unique

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness

namespace SupercriticalConformalCovariance.Rotation

/-- DG Proposition 1.9 up to its deterministic multiplicative constant. -/
theorem exists_rotation_constant
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (a : ℂ) (ha : ‖a‖ = 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsGFFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ u v : ℂ,
          (D (GaussianLQG.rotDist a (h ω))).1
            (a⁻¹ * u, a⁻¹ * v) =
          ENNReal.ofReal C * (D (h ω)).1 (u, v) := by
  obtain ⟨C, hC, hEq⟩ :=
    strongLQGMetric_unique ξ Q hQ D
      (rotatedAssignment a (GaussianLQG.ne_zero_of_norm_eq_one ha) D)
      hD (isStrong_rotatedAssignment hD ha)
  refine ⟨C, hC, ?_⟩
  intro Ω mΩ P iP h hh
  filter_upwards [hEq P h hh] with ω hω u v
  exact hω u v


end SupercriticalConformalCovariance.Rotation
