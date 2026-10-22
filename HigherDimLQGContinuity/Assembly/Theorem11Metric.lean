import HigherDimLQGContinuity.Discharge.Theorem11
import HigherDimLQGContinuity.SiteCert.Holds

/-!
# Provider of the frozen theorem `HigherDimLQGContinuity.theorem11_metric`

`theorem11_metric_impl` states the frozen anchor `HigherDimLQGContinuity/Frozen/Theorem11Metric.lean` verbatim (copied programmatically with
the anchor's `open` lines). Proof: the orchestrator's assembly `theorem11Metric_of_siteCert` (`Discharge/Theorem11.lean`) applied to the site
certificate `siteCert_holds` (packet Q7b). This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The frozen statement of `theorem11_metric`, proved. -/
theorem theorem11_metric_impl :
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ γ : ℝ, 0 < γ → γ < Real.sqrt (2 * d) →
        ∀ ξ : ℝ, 0 < ξ → distExp d ξ = (d : ℝ) / γ + γ / 2 →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D γ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, (∀ γ₀ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∀ R : ℝ, 0 < R →
            Tendsto (fun γ => supDistLU d R (D γ (h ω)) (D γ₀ (h ω)))
              (𝓝[Ico (0 : ℝ) (Real.sqrt (2 * d))] γ₀) (𝓝 0)) ∧
          ∀ γ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∃ M : ContMetric d, M.1 = D γ (h ω) ∧ M.IsLength := by
  exact theorem11Metric_of_siteCert fun _d hd => siteCert_holds hd

end HigherDimLQGContinuity
