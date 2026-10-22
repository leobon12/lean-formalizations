import HigherDimLQGContinuity.Discharge.Theorem11
import HigherDimLQGContinuity.SiteCert.Holds

/-!
# Provider of the frozen theorem `HigherDimLQGContinuity.theorem11Xi`

`theorem11Xi_impl` states the frozen anchor `HigherDimLQGContinuity/Frozen/Theorem11Xi.lean` verbatim (copied programmatically with
the anchor's `open` lines). Proof: the orchestrator's assembly `theorem11Xi_of_siteCert` (`Discharge/Theorem11.lean`) applied to the site
certificate `siteCert_holds` (packet Q7b). This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The frozen statement of `theorem11Xi`, proved. -/
theorem theorem11Xi_impl :
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D ξ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ ξ₀ ∈ xiRange d, ∀ R : ℝ, 0 < R →
          Tendsto (fun ξ => supDistLU d R (D ξ (h ω)) (D ξ₀ (h ω))) (𝓝[xiRange d] ξ₀) (𝓝 0) := by
  exact theorem11Xi_of_siteCert fun _d hd => siteCert_holds hd

end HigherDimLQGContinuity
