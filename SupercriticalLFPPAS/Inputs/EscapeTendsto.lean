import SupercriticalLFPPAS.Inputs.Escape

/-! The filter formulation of escape to infinite metric distance. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLFPPAS

open SupercriticalLQGUniqueness
open LQGMetric (DistC)

/-- Almost surely, for each integer `k`, the distance from the closed Euclidean `k`-ball
to the concentric sphere of radius `R` converges to infinity as `R → ∞`. -/
theorem ae_d2EscapeSetDist_tendsto
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      Tendsto
        (fun R : ℝ =>
          SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
            (D (h ω)) (Metric.closedBall (0 : ℂ) k) (Metric.sphere (0 : ℂ) R))
        atTop (nhds (⊤ : ℝ≥0∞)) := by
  filter_upwards [ae_d2EscapeSetDist hD P h hh] with ω hω
  intro k
  refine ENNReal.tendsto_nhds_top fun M => ?_
  obtain ⟨R₀, hR₀⟩ := hω k M
  exact eventually_atTop.2 ⟨R₀, hR₀⟩

end SupercriticalLFPPAS
