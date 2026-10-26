import SupercriticalLFPPAS.Inputs.RationalCirclePositive

/-!
# Finiteness of distances between rational circles

For disjoint positive-radius rational circles this reuses the positive finite
set-distance result.  Intersecting circles have set-distance zero.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness

namespace SupercriticalLFPPAS

/-- The Euclidean circle with rational center coordinates and rational radius. -/
def rationalCircle (q : ℚ × ℚ) (r : ℚ) : Set ℂ :=
  Metric.sphere ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) (r : ℝ)

/-- Almost surely, two fixed positive-radius rational circles have finite metric
set-distance.  When the circles intersect, their set-distance is zero. -/
theorem ae_rationalCircleDistance_lt_top
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (q₁ q₂ : ℚ × ℚ) (r₁ r₂ : ℚ) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) :
    ∀ᵐ ω ∂P,
      B2.Iface.setDistance (D (h ω)).1
        (rationalCircle q₁ r₁) (rationalCircle q₂ r₂) < ⊤ := by
  classical
  by_cases hdis : Disjoint (rationalCircle q₁ r₁) (rationalCircle q₂ r₂)
  · filter_upwards
      [Inputs.ae_setDist_rationalCircle_pos_lt_top hD P h hh q₁ q₂ r₁ r₂ hr₁ hr₂ hdis]
      with ω hω
    change SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
      (D (h ω)) (rationalCircle q₁ r₁) (rationalCircle q₂ r₂) < ⊤
    exact hω.2
  · obtain ⟨p, hp₁, hp₂⟩ := not_disjoint_iff.1 hdis
    refine ae_of_all P fun ω => ?_
    have hzero :
        B2.Iface.setDistance (D (h ω)).1
            (rationalCircle q₁ r₁) (rationalCircle q₂ r₂) = 0 := by
      apply le_antisymm
      · exact iInf₂_le_of_le p hp₁
          (iInf₂_le_of_le p hp₂ ((D (h ω)).isExtMetric.1 p).le)
      · exact bot_le
    rw [hzero]
    exact ENNReal.zero_lt_top

end SupercriticalLFPPAS
