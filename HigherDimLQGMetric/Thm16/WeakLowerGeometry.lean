import HigherDimLQGMetric.Thm16.LfppScaleLower
import HigherDimLQGMetric.Events.TightLaw
import HigherDimLQGMetric.Metric.ContMetric

/-! Off-diagonal lower control of a scaled weak metric bounds set distances. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

theorem l9c_setDistIn_scaled_lower {d : ℕ}
    (ξ : ℝ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ)
    (h : DistRd d) {r q η : ℝ} (hr : 0 < r) (hq : q ≤ r / 4)
    (hc : 0 < c r)
    (hlo : ∀ p ∈ closedBall (e₁ d) (1 / 4) ×ˢ
        closedBall (-e₁ d) (1 / 4),
        η ≤ scaledField ξ D c r 0 h p)
    (V : Set (Rd d)) :
    ENNReal.ofReal (c r * Real.exp (ξ * sphereAvg h r 0) * η) ≤
      setDistIn (D h) V
        (ball (r • e₁ d) q) (ball (-(r • e₁ d)) q) := by
  unfold setDistIn
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  let u := r⁻¹ • x
  let v := r⁻¹ • y
  have hux : u ∈ closedBall (e₁ d) (1 / 4) := l9c_ball_scale_left hr hq hx
  have hvy : v ∈ closedBall (-e₁ d) (1 / 4) := l9c_ball_scale_right hr hq hy
  have hx' : r • u = x := by dsimp [u]; rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hy' : r • v = y := by dsimp [v]; rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hlo' := hlo (u, v) ⟨hux, hvy⟩
  rw [scaledField_zero] at hlo'
  have hscaled : η ≤ (c r)⁻¹ * Real.exp (-ξ * sphereAvg h r 0) * (D h).1 (x,y) := by
    change η ≤ (c r)⁻¹ * Real.exp (-ξ * sphereAvg h r 0) *
      (D h).1 (r • u, r • v) at hlo'
    simpa only [hx', hy'] using hlo'
  have hfac : 0 < c r * Real.exp (ξ * sphereAvg h r 0) :=
    mul_pos hc (Real.exp_pos _)
  have hreal : c r * Real.exp (ξ * sphereAvg h r 0) * η ≤ (D h).1 (x,y) := by
    have hmul := mul_le_mul_of_nonneg_left hscaled hfac.le
    have hcancel : (c r * Real.exp (ξ * sphereAvg h r 0)) *
        ((c r)⁻¹ * Real.exp (-ξ * sphereAvg h r 0) * (D h).1 (x,y)) =
        (D h).1 (x,y) := by
      rw [show -ξ * sphereAvg h r 0 = -(ξ * sphereAvg h r 0) by ring,
        Real.exp_neg]
      field_simp [hc.ne']
    rwa [hcancel] at hmul
  exact (ENNReal.ofReal_le_ofReal hreal).trans ((D h).ofReal_le_internal V x y)

end HigherDimLQGMetric
