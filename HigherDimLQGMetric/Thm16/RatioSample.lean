import HigherDimLQGMetric.Thm16.LfppUpperGeometry
import HigherDimLQGMetric.Thm16.WeakUpperGeometry
import HigherDimLQGMetric.Thm16.WeakLowerGeometry
import HigherDimLQGMetric.Thm16.RatioIneq

/-! Deterministic cancellation of the two comparisons on one sample. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

private theorem l9c_sphere_left {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    r • e₁ d ∈ sphere (0 : Rd d) r := by
  rw [mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, HigherDimLFPP.norm_e₁ hd]
  ring

private theorem l9c_sphere_right {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    -(r • e₁ d) ∈ sphere (0 : Rd d) r := by
  rw [mem_sphere, dist_eq_norm, sub_zero, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, HigherDimLFPP.norm_e₁ hd]
  ring

theorem l9c_ratio_upper_sample {d : ℕ} (hd : 0 < d)
    (κ : Rd d → ℝ) (ξ ε : ℝ) (h g : DistRd d)
    (D : DistRd d → ContMetric d) (c a : ℝ → ℝ)
    {r q C M η : ℝ} (hr : 0 < r) (hq : q ≤ r / 4)
    (hC : 0 < C) (hM : 0 ≤ M) (hη : 0 < η)
    (hc : 0 < c r) (haε : 0 < a ε) (haδ : 0 < a (ε / r))
    (hφ : Continuous (convMollify κ ε h))
    (hscale : ∀ u v : Rd d,
      lfppDist κ ξ ε h (r • u, r • v) =
        r * Real.exp (ξ * sphereAvg h r 0) *
          lfppDist κ ξ (ε / r) g (u, v))
    (hlo : ∀ p ∈ closedBall (e₁ d) (1 / 4) ×ˢ
        closedBall (-e₁ d) (1 / 4),
        η < (a (ε / r))⁻¹ * lfppDist κ ξ (ε / r) g p)
    {U : Set (Rd d)} (hU : ann (0 : Rd d) (r / 2) (2 * r) ⊆ U)
    (hDgood : sphereDiam (weakScaledMetric ξ D c h hr 0 hc) 0 1 ≤ ENNReal.ofReal M)
    (hprop : ENNReal.ofReal (a ε)⁻¹ *
        lfppSetDistIn κ ξ ε h (thickening q U)
          (ball (r • e₁ d) q) (ball (-(r • e₁ d)) q) ≤
        ENNReal.ofReal C * (D h).internal U (r • e₁ d) (-(r • e₁ d))) :
    l9c_ratio a ε r ≤ (C * M / η) * c r := by
  have hlfpp := l9c_lfppSetDistIn_scaled_lower κ ξ ε h g hφ hr hq
    haδ hscale hlo (thickening q U)
  have hD := l9c_internal_le_scaledSphereDiam ξ D c h hr hc hM hDgood
    hU (l9c_sphere_left hd hr) (l9c_sphere_right hd hr)
  have hineq : ENNReal.ofReal (a ε)⁻¹ *
      ENNReal.ofReal (r * Real.exp (ξ * sphereAvg h r 0) * a (ε / r) * η) ≤
      ENNReal.ofReal C *
        ENNReal.ofReal (c r * Real.exp (ξ * sphereAvg h r 0) * M) := by
    exact (mul_le_mul_right hlfpp _).trans
      (hprop.trans (mul_le_mul_right hD _))
  exact l9c_ratio_upper_algebra haε hc (Real.exp_pos _) hη hM hC.le hineq

theorem l9c_ratio_lower_sample {d : ℕ} (hd : 2 ≤ d)
    (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d)
    (D : DistRd d → ContMetric d) (c a : ℝ → ℝ)
    {r q C M η : ℝ} (hr : 0 < r) (hq : q ≤ r / 4)
    (hC : 0 < C) (hM : 0 ≤ M) (hη : 0 < η)
    (hc : 0 < c r) (haε : 0 < a ε) (haδ : 0 < a (ε / r))
    (hφ : Continuous (convMollify κ ε h))
    (hDlo : ∀ p ∈ closedBall (e₁ d) (1 / 4) ×ˢ
        closedBall (-e₁ d) (1 / 4), η ≤ scaledField ξ D c r 0 h p)
    {U : Set (Rd d)} (hU : ann (0 : Rd d) (r / 2) (2 * r) ⊆ U)
    (hLfpp : DGZ.lfppDiam ξ (convMollify κ ε h)
        (sphere (0 : Rd d) r) (ann 0 (r / 2) (2 * r)) ≤
        M * (r * a (ε / r)) * Real.exp (ξ * sphereAvg h r 0))
    (hprop : setDistIn (D h) (thickening q U)
        (ball (r • e₁ d) q) (ball (-(r • e₁ d)) q) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal (a ε)⁻¹ *
          lfppDistIn κ ξ ε h U (r • e₁ d) (-(r • e₁ d)))) :
    c r ≤ (C * M / η) * l9c_ratio a ε r := by
  have hD := l9c_setDistIn_scaled_lower ξ D c h hr hq hc hDlo (thickening q U)
  have hLfpp' := l9c_lfppDistIn_le_sphereDiam hd κ ξ ε h hφ hr hU
    (l9c_sphere_left (by omega : 0 < d) hr)
    (l9c_sphere_right (by omega : 0 < d) hr)
  have hUpper : lfppDistIn κ ξ ε h U (r • e₁ d) (-(r • e₁ d)) ≤
      ENNReal.ofReal (r * Real.exp (ξ * sphereAvg h r 0) * a (ε / r) * M) := by
    calc
      _ ≤ ENNReal.ofReal (DGZ.lfppDiam ξ (convMollify κ ε h)
        (sphere (0 : Rd d) r) (ann 0 (r / 2) (2 * r))) := hLfpp'
      _ ≤ ENNReal.ofReal (M * (r * a (ε / r)) * Real.exp (ξ * sphereAvg h r 0)) :=
        ENNReal.ofReal_le_ofReal hLfpp
      _ = _ := by congr 1; ring
  have hineq : ENNReal.ofReal (c r * Real.exp (ξ * sphereAvg h r 0) * η) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal (a ε)⁻¹ *
          ENNReal.ofReal (r * Real.exp (ξ * sphereAvg h r 0) * a (ε / r) * M)) := by
    exact hD.trans (hprop.trans (mul_le_mul_right
      (mul_le_mul_right hUpper _) _))
  exact l9c_ratio_lower_algebra haε haδ (Real.exp_pos _) hη hM hC.le hr hineq

end HigherDimLQGMetric
