import HigherDimLQGContinuity.MarginalEuclid.UnitLaw
import HigherDimLQGContinuity.Norm.PinGauss

/-!
# Exact representation of a normalized distance at one pair

The metric at `(x, x + r • u)` is the exact scale factor times a unit
distance in the recentred field. Under the unit pin, the recentred field
has the unit-pinned law and the scale factor's sphere average is Gaussian.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- Exact pair representation at the unit pin. -/
theorem rho_pair_repr {d : ℕ} (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {r : ℝ} (hr : 0 < r) (x u : Rd d) :
    ∀ᵐ g ∂(normLGFLaw d),
      (rho D g).1 (x, x + r • u) =
        r ^ phiXi d ξ * Real.exp (ξ * sphereAvg g r x) *
          (rho D (recentre 1 r x g)).1 (0, u) := by
  rw [← pinLaw_one (by omega : 2 ≤ d)]
  filter_upwards [rho_pair_scaling (by omega : 2 ≤ d) hξ hD
    (s := 1) one_pos hr x u] with g hg
  simpa only [one_mul, scaleS] using hg

/-- The unit distance in the recentred field has the unit-distance law. -/
theorem law_rho_pair_unit {d : ℕ} (hd : 3 ≤ d) (hR : StrongRotLaw d)
    {ξ : ℝ} (hξ : 0 < ξ) (hgap : Real.sqrt (2 * d) < distExp d ξ)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {r : ℝ} (hr : 0 < r) (x u : Rd d) (hu : ‖u‖ = 1) :
    (normLGFLaw d).map (fun g => (rho D (recentre 1 r x g)).1 (0, u)) =
      (normLGFLaw d).map (fun g => (rho D g).1 (0, e₁ d)) := by
  have hm : Measurable (fun g : DistRd d => (rho D g).1 (0, u)) :=
    p2_measurable_contMetric_apply (measurable_rho hD.measurable) (0, u)
  calc
    (normLGFLaw d).map (fun g => (rho D (recentre 1 r x g)).1 (0, u)) =
        (pinLaw d 1).map (fun g => (rho D g).1 (0, u)) := by
      rw [← pinLaw_one (by omega : 2 ≤ d)]
      exact map_comp_recentre (by omega : 2 ≤ d) hm one_pos one_pos hr x
    _ = (normLGFLaw d).map (fun g => (rho D g).1 (0, e₁ d)) := by
      rw [pinLaw_one (by omega : 2 ≤ d)]
      exact law_rho_unit hd hR hξ hgap hD hu

/-- The spherical factor in the pair representation is centred Gaussian under the unit pin. -/
theorem pair_sphereAvg_gaussian {d : ℕ} (hd : 3 ≤ d) {r : ℝ} (hr : 0 < r) (x : Rd d) :
    HasGaussianLaw (fun g : DistRd d => sphereAvg g r x) (normLGFLaw d) ∧
      ∫ g, sphereAvg g r x ∂(normLGFLaw d) = 0 := by
  rw [← pinLaw_one (by omega : 2 ≤ d)]
  exact hasGaussianLaw_sphereAvg_pinLaw (by omega : 2 ≤ d) one_pos hr x

/-- A dimension-dependent variance constant for every pair scale at the unit pin. -/
theorem exists_pair_sphereAvg_variance_le {d : ℕ} (hd : 3 ≤ d) :
    ∃ K : ℝ, ∀ {r : ℝ}, 0 < r → ∀ x : Rd d,
      (r ≤ 1 → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log (1 / r) + 2 * max 0 (Real.log ‖x‖) + K) ∧
      (1 ≤ r → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log r + 2 * max 0 (Real.log (‖x‖ / r)) + K) := by
  obtain ⟨K, hK⟩ := exists_variance_sphereAvg_pinLaw_le (by omega : 2 ≤ d)
  refine ⟨K, fun {r} hr x => ?_⟩
  rw [← pinLaw_one (by omega : 2 ≤ d)]
  simpa only [div_one] using hK one_pos hr x

end HigherDimLQGContinuity
