import HigherDimLQGContinuity.Param.Prop18

/-!
# Provider of the frozen theorem `HigherDimLQGContinuity.prop18`

`prop18_impl` states the frozen anchor `HigherDimLQGContinuity/Frozen/Prop18.lean` verbatim (the γ ↔ ξ parametrization,
[C] (1.5)). Proof: packet PAR's `prop18_holds` (`Param/Prop18.lean`; NA1's repair R1: ϕ = ξQ(ξ) is √(2d)-Lipschitz with
ϕ(0) = 1; ruling N3). This module imports no frozen theorem anchor.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- The frozen statement of `prop18`, proved. -/
theorem prop18_impl :
    ∀ d : ℕ, 3 ≤ d →
      ContinuousOn (distExp d) (Ioi 0) ∧
      StrictAntiOn (distExp d) {ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ} ∧
      Tendsto (fun ξ => ξ * distExp d ξ) (𝓝[>] 0) (𝓝 1) ∧
      ∃ Ξ : ℝ → ℝ, Ξ 0 = 0 ∧
        StrictMonoOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        ContinuousOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        Ξ '' Ico 0 (Real.sqrt (2 * d)) = xiRange d ∧
        (∀ γ ∈ Ioo (0 : ℝ) (Real.sqrt (2 * d)), ∀ ξ : ℝ, 0 < ξ →
          (distExp d ξ = (d : ℝ) / γ + γ / 2 ↔ ξ = Ξ γ)) ∧
        Tendsto (fun γ => γ / Ξ γ) (𝓝[>] 0) (𝓝 (d : ℝ)) := by
  exact prop18_holds

end HigherDimLQGContinuity
