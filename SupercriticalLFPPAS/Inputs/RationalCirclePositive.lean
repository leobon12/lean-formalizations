import SupercriticalLFPPAS.Inputs.RationalCircleBounds

/-!
# Positive finite distance between rational Euclidean circles

This is the rational-coordinate specialization of the corresponding result for
arbitrary fixed Euclidean circles.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLFPPAS.Inputs

open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios

/-- Almost surely, two fixed disjoint Euclidean circles with rational centers and
strictly positive rational radii have strictly positive finite metric set-distance. -/
theorem ae_setDist_rationalCircle_pos_lt_top
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (q₁ q₂ : ℚ × ℚ) (r₁ r₂ : ℚ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hdis : Disjoint
      (Metric.sphere ((q₁.1 : ℂ) + (q₁.2 : ℂ) * Complex.I) (r₁ : ℝ))
      (Metric.sphere ((q₂.1 : ℂ) + (q₂.2 : ℂ) * Complex.I) (r₂ : ℝ))) :
    ∀ᵐ ω ∂P,
      0 < setDist (D (h ω))
          (Metric.sphere ((q₁.1 : ℂ) + (q₁.2 : ℂ) * Complex.I) (r₁ : ℝ))
          (Metric.sphere ((q₂.1 : ℂ) + (q₂.2 : ℂ) * Complex.I) (r₂ : ℝ)) ∧
        setDist (D (h ω))
          (Metric.sphere ((q₁.1 : ℂ) + (q₁.2 : ℂ) * Complex.I) (r₁ : ℝ))
          (Metric.sphere ((q₂.1 : ℂ) + (q₂.2 : ℂ) * Complex.I) (r₂ : ℝ)) < ⊤ := by
  exact RationalCircleBounds.ae_setDist_circle_pos_lt_top hD P h hh
    ((q₁.1 : ℂ) + (q₁.2 : ℂ) * Complex.I)
    ((q₂.1 : ℂ) + (q₂.2 : ℂ) * Complex.I)
    (Rat.cast_pos.mpr hr₁) (Rat.cast_pos.mpr hr₂) hdis

end SupercriticalLFPPAS.Inputs
