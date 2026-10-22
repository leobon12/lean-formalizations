import HigherDimLQGMetric.Thm16.LfppGeometry
import HigherDimLQGMetric.Thm16.LfppLower

/-! The lower tail of scaled point distances bounds LFPP set distances. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l9c_ball_scale_left {d : ℕ} {r q : ℝ}
    (hr : 0 < r) (hq : q ≤ r / 4) {x : Rd d}
    (hx : x ∈ ball (r • e₁ d) q) :
    r⁻¹ • x ∈ closedBall (e₁ d) (1 / 4) := by
  have heq : r⁻¹ • x - e₁ d = r⁻¹ • (x - r • e₁ d) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [mem_closedBall, dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr]
  have hdist : ‖x - r • e₁ d‖ < q := by
    simpa only [mem_ball, dist_eq_norm] using hx
  have hq' : ‖x - r • e₁ d‖ ≤ r / 4 := hdist.le.trans hq
  have hdiv : ‖x - r • e₁ d‖ / r ≤ (1 / 4 : ℝ) := by
    exact (div_le_iff₀ hr).2 (by nlinarith)
  simpa only [inv_mul_eq_div] using hdiv

theorem l9c_ball_scale_right {d : ℕ} {r q : ℝ}
    (hr : 0 < r) (hq : q ≤ r / 4) {y : Rd d}
    (hy : y ∈ ball (-(r • e₁ d)) q) :
    r⁻¹ • y ∈ closedBall (-e₁ d) (1 / 4) := by
  have heq : r⁻¹ • y - -e₁ d = r⁻¹ • (y - -(r • e₁ d)) := by
    rw [smul_sub, smul_neg, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [mem_closedBall, dist_eq_norm, heq, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hr]
  have hdist : ‖y - -(r • e₁ d)‖ < q := by
    simpa only [mem_ball, dist_eq_norm] using hy
  have hq' : ‖y - -(r • e₁ d)‖ ≤ r / 4 := hdist.le.trans hq
  have hdiv : ‖y - -(r • e₁ d)‖ / r ≤ (1 / 4 : ℝ) := by
    exact (div_le_iff₀ hr).2 (by nlinarith)
  simpa only [inv_mul_eq_div] using hdiv

theorem l9c_lfppSetDistIn_scaled_lower {d : ℕ}
    (κ : Rd d → ℝ) (ξ ε : ℝ) (h g : DistRd d)
    (hφ : Continuous (convMollify κ ε h))
    {r q a η : ℝ} (hr : 0 < r) (hq : q ≤ r / 4)
    (ha : 0 < a)
    (hscale : ∀ u v : Rd d,
      lfppDist κ ξ ε h (r • u, r • v) =
        r * Real.exp (ξ * sphereAvg h r 0) *
          lfppDist κ ξ (ε / r) g (u, v))
    (hlo : ∀ p ∈ closedBall (e₁ d) (1 / 4) ×ˢ
        closedBall (-e₁ d) (1 / 4),
        η < a⁻¹ * lfppDist κ ξ (ε / r) g p)
    (V : Set (Rd d)) :
    ENNReal.ofReal (r * Real.exp (ξ * sphereAvg h r 0) * a * η) ≤
      lfppSetDistIn κ ξ ε h V
        (ball (r • e₁ d) q) (ball (-(r • e₁ d)) q) := by
  apply l9c_lfppSetDistIn_lower κ ξ ε h hφ V
  intro x hx y hy
  have hux := l9c_ball_scale_left hr hq hx
  have hvy := l9c_ball_scale_right hr hq hy
  let u := r⁻¹ • x
  let v := r⁻¹ • y
  have hx' : r • u = x := by dsimp [u]; rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hy' : r • v = y := by dsimp [v]; rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hlo' := hlo (u, v) ⟨hux, hvy⟩
  have hdist : a * η ≤ lfppDist κ ξ (ε / r) g (u, v) := by
    calc
      a * η ≤ a * (a⁻¹ * lfppDist κ ξ (ε / r) g (u, v)) :=
        mul_le_mul_of_nonneg_left hlo'.le ha.le
      _ = lfppDist κ ξ (ε / r) g (u, v) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  rw [←hx', ←hy', hscale]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left hdist
      (mul_pos hr (Real.exp_pos (ξ * sphereAvg h r 0))).le)

end HigherDimLQGMetric
