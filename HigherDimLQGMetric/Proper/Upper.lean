import HigherDimLQGMetric.Proper.ConfineDet

/-!
# Uniform upper bounds on metric diameters in Euclidean balls

This transfers the compact-set tightness bound for normalized metrics to the original metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Rescaling the endpoints of a Euclidean ball puts them in the fixed unit-scale ball. -/
theorem proper_rescale_ball {R L : ℝ} (hR : 0 < R) {x : Rd d}
    (hx : ‖x‖ < L * R) :
    R • (R⁻¹ • x) = x ∧ R⁻¹ • x ∈ Metric.closedBall (0 : Rd d) L := by
  have heq : R • (R⁻¹ • x) = x := by
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  refine ⟨heq, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hR)]
  exact (inv_mul_lt_iff₀ hR).2 (by nlinarith [hx]) |>.le

/-- A normalized upper bound gives the corresponding original-distance bound. -/
theorem proper_dist_upper_of_normalized (ξ Q : ℝ) (D : DistRd d → ContMetric d)
    (h : DistRd d) {R L b : ℝ} (hR : 0 < R) {x y : Rd d}
    (hx : ‖x‖ < L * R) (hy : ‖y‖ < L * R)
    (hG : normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) h R
      (R⁻¹ • x, R⁻¹ • y) < b) :
    (D h).1 (x, y) < b * sNorm ξ Q h R 0 := by
  obtain ⟨hex, -⟩ := proper_rescale_ball hR hx
  obtain ⟨hey, -⟩ := proper_rescale_ball hR hy
  have heq := proper_normalized_mul ξ Q D h hR (R⁻¹ • x) (R⁻¹ • y)
  rw [hex, hey] at heq
  calc
    (D h).1 (x, y) = sNorm ξ Q h R 0 *
        normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) h R
          (R⁻¹ • x, R⁻¹ • y) := heq.symm
    _ < sNorm ξ Q h R 0 * b :=
      mul_lt_mul_of_pos_left hG (proper_sNorm_pos ξ Q h hR)
    _ = b * sNorm ξ Q h R 0 := mul_comm _ _

/-- Tightness supplies a uniform upper bound on all distances between points of the base ball. -/
theorem proper_exists_ball_upper {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (L : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧ ∀ R : ℝ, 0 < R →
      P {ω | ¬ ∀ x y : Rd d, ‖x‖ < L * R → ‖y‖ < L * R →
        (D (h ω)).1 (x, y) < b * sNorm ξ Q (h ω) R 0} < ε := by
  obtain ⟨b, hb, hraw⟩ := proper_exists_diameter_upper P h hD hh L hε
  refine ⟨b, hb, fun R hR => ?_⟩
  refine lt_of_le_of_lt (measure_mono ?_) (hraw R hR)
  intro ω hbad
  push Not at hbad
  obtain ⟨x, y, hx, hy, hxy⟩ := hbad
  obtain ⟨-, hx'⟩ := proper_rescale_ball hR hx
  obtain ⟨-, hy'⟩ := proper_rescale_ball hR hy
  refine ⟨R⁻¹ • x, hx', R⁻¹ • y, hy', ?_⟩
  by_contra hnot
  have hG : normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) (h ω) R
      (R⁻¹ • x, R⁻¹ • y) < b := lt_of_not_ge hnot
  exact (not_lt_of_ge hxy) (proper_dist_upper_of_normalized ξ Q D (h ω) hR hx hy hG)

end HigherDimLQGMetric
