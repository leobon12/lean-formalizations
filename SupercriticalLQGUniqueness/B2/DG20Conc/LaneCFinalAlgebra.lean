import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCENNScaleCancel

 
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneC_normalized_L2_deterministic_rate
    {ell ξ Q δ p ζ ν : ℝ} (hell : 0 < ell)
    (hp : 0 < p) (hζ : 0 < ζ) (K : ℕ) :
    let q : ℝ := 2 * ((1 + ζ) / ζ)
    let t : ℝ := ζ / (2 * (1 + ζ))
    let a : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + δ) * (K : ℝ)) * ell
    let s : ℝ := (2 : ℝ)⁻¹ ^ K * ell
    let E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ν * K) + 1)
    let G : ℝ≥0∞ := (ENNReal.ofReal
      (Real.exp (((K : ℝ) * Real.log 2) *
        (((1 + ζ) * p * ξ) ^ 2) / 2))) ^ (1 / (1 + ζ))
    (ENNReal.ofReal a ^ p)⁻¹ ^ (2 : ℝ) *
      (E ^ (2 * t) *
        (ENNReal.ofReal (s ^ (p * q)) * E) ^ (2 * t) * G ^ (2 : ℝ)) =
      ENNReal.ofReal ((2 : ℝ) ^
        (((1 + ζ) * p ^ 2 * ξ ^ 2 - 2 * p * ξ * Q + 2 * p * δ) * K)) *
        E ^ (4 * t) := by
  let q : ℝ := 2 * ((1 + ζ) / ζ)
  let t : ℝ := ζ / (2 * (1 + ζ))
  let a : ℝ := (2 : ℝ) ^ (-(1 - ξ * Q + δ) * (K : ℝ)) * ell
  let s : ℝ := (2 : ℝ)⁻¹ ^ K * ell
  let E : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ν * K) + 1)
  let G : ℝ≥0∞ := (ENNReal.ofReal
    (Real.exp (((K : ℝ) * Real.log 2) *
      (((1 + ζ) * p * ξ) ^ 2) / 2))) ^ (1 / (1 + ζ))
  have hζ1 : 0 < 1 + ζ := by linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hqt : q * t = 1 := by
    dsimp [q, t]
    field_simp
  have hs : 0 < s := mul_pos (by positivity) hell
  have ha : 0 < a := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hell
  have hE0 : E ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hETop : E ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpq : 0 ≤ p * q := mul_nonneg hp.le hq.le
  have hqpow : ENNReal.ofReal (s ^ (p * q)) = ENNReal.ofReal s ^ (p * q) := by
    exact (ENNReal.ofReal_rpow_of_nonneg hs.le hpq).symm
  change (ENNReal.ofReal a ^ p)⁻¹ ^ (2 : ℝ) *
      (E ^ (2 * t) * (ENNReal.ofReal (s ^ (p * q)) * E) ^ (2 * t) * G ^ (2 : ℝ)) =
    ENNReal.ofReal ((2 : ℝ) ^
      (((1 + ζ) * p ^ 2 * ξ ^ 2 - 2 * p * ξ * Q + 2 * p * δ) * K)) * E ^ (4 * t)
  rw [hqpow]
  have hscale := laneC_scale_power_cancel
    (ENNReal.ofReal a) (ENNReal.ofReal s) E hp.le ht.le hqt
  have hrate := laneC_ennreal_scale_cancel (ell := ell) (ξ := ξ)
    (Q := Q) (δ := δ) (p := p) hell hp.le K
  have hgauss := laneC_gaussian_rate_power K ζ p ξ hζ
  calc
    _ = (((ENNReal.ofReal a ^ p)⁻¹) ^ (2 : ℝ) *
        ((ENNReal.ofReal s ^ (p * q) * E) ^ (2 * t))) *
        (E ^ (2 * t) * G ^ (2 : ℝ)) := by ac_rfl
    _ = ((ENNReal.ofReal s / ENNReal.ofReal a) ^ (2 * p) *
        E ^ (2 * t)) * (E ^ (2 * t) * G ^ (2 : ℝ)) := by rw [hscale]
    _ = (ENNReal.ofReal ((2 : ℝ) ^ ((-ξ * Q + δ) * (2 * p) * K)) *
        E ^ (4 * t)) *
        ENNReal.ofReal ((2 : ℝ) ^ (((1 + ζ) * p ^ 2 * ξ ^ 2) * K)) := by
      rw [hrate, hgauss]
      rw [show (4 : ℝ) * t = 2 * t + 2 * t by ring,
        ENNReal.rpow_add (2 * t) (2 * t) hE0 hETop]
      ac_rfl
    _ = _ := by
      have htwo : 0 < (2 : ℝ) := by norm_num
      rw [mul_assoc, mul_comm (E ^ (4 * t)) _, ← mul_assoc]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg htwo.le _)]
      rw [← Real.rpow_add htwo]
      congr 2
      ring

end SupercriticalLQGUniqueness.B2.DG20Conc
