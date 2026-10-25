import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteCostTransport
import SupercriticalLQGUniqueness.B2.Polylog.P4Event

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalizedContLFPP_edist_eq_lfppMetric
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (x y : ℂ) :
    edist ((normalizedContLFPP ξ a φ).pt x)
      ((normalizedContLFPP ξ a φ).pt y) =
        B2.Median.lfppMetric ξ a φ (x, y) := by
  rw [ContMetric.edist_pt, B2.Median.lfppMetric_apply,
    B2.LscTop.lfppDistance_eq_lfppD,
    normalizedContLFPP, ContMetric.smulPos_apply,
    LQGMetric.LFPP.lfppContMetric_apply]
  rw [ENNReal.ofReal_mul (inv_pos.mpr a.property).le,
    ENNReal.ofReal_toReal (LQGMetric.LFPP.lfppD_ne_top φ.continuous x y)]

 
theorem normalizedContLFPP_affine_edist
    (ξ : ℝ) (a a' : Ioi (0 : ℝ))
    {φ φ' : C(ℂ, ℝ)} {b c : ℂ} (hc : c ≠ 0)
    (k₀ : ℝ)
    (hφ : ∀ x, φ' x = φ (b + c * x) + k₀)
    (x y : ℂ) :
    edist ((normalizedContLFPP ξ a' φ').pt x)
      ((normalizedContLFPP ξ a' φ').pt y) =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) /
        ((a' : ℝ) * ‖c‖)) *
        edist ((normalizedContLFPP ξ a φ).pt (b + c * x))
          ((normalizedContLFPP ξ a φ).pt (b + c * y)) := by
  rw [normalizedContLFPP_edist_eq_lfppMetric,
    normalizedContLFPP_edist_eq_lfppMetric]
  exact B2.Polylog.lfppMetric_affine ξ a a' hc k₀ hφ x y

 

theorem normalizedContLFPP_affine_costs
    (ξ : ℝ) (a a' : Ioi (0 : ℝ))
    {φ φ' : C(ℂ, ℝ)} {b c : ℂ} (hc : c ≠ 0)
    (k₀ : ℝ) (hφ : ∀ x, φ' x = φ (b + c * x) + k₀)
    (T : ℂ ≃ₜ ℂ) (hT : ∀ x, T x = b + c * x)
    (A E F : Set ℂ) :
    (normalizedContLFPP ξ a' φ').aroundDist A E F =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) /
        ((a' : ℝ) * ‖c‖)) *
        (normalizedContLFPP ξ a φ).aroundDist
          (T '' A) (T '' E) (T '' F) ∧
    LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a' φ') E F =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) /
        ((a' : ℝ) * ‖c‖)) *
        LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a φ)
          (T '' E) (T '' F) := by
  have hκ : 0 < (a : ℝ) * Real.exp (ξ * k₀) /
      ((a' : ℝ) * ‖c‖) := by
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    exact div_pos (mul_pos a.property (Real.exp_pos _))
      (mul_pos a'.property hcn)
  have h0 : ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) /
      ((a' : ℝ) * ‖c‖)) ≠ 0 := (ENNReal.ofReal_pos.mpr hκ).ne'
  have hm : ∀ x y : ℂ,
      edist ((normalizedContLFPP ξ a' φ').pt x)
        ((normalizedContLFPP ξ a' φ').pt y) =
      ENNReal.ofReal ((a : ℝ) * Real.exp (ξ * k₀) /
        ((a' : ℝ) * ‖c‖)) *
        edist ((normalizedContLFPP ξ a φ).pt (T x))
          ((normalizedContLFPP ξ a φ).pt (T y)) := by
    intro x y
    rw [hT x, hT y]
    exact normalizedContLFPP_affine_edist ξ a a' hc k₀ hφ x y
  exact ⟨aroundDist_comp_homeomorph_mul h0 ENNReal.ofReal_ne_top T hm A E F,
    setDist_comp_homeomorph_mul h0 ENNReal.ofReal_ne_top T hm E F⟩

private theorem good_cost_iff_common_mul
    (k C R S : ℝ≥0∞) (hk0 : k ≠ 0) (hkt : k ≠ ∞) :
    C * (k * S) < k * R ↔ C * S < R := by
  have hcoeff : C * (k * S) = k * (C * S) := by ac_rfl
  rw [hcoeff]
  have hcanc (x : ℝ≥0∞) : (k * x) * k⁻¹ = x := by
    calc
      (k * x) * k⁻¹ = (k⁻¹ * k) * x := by ac_rfl
      _ = x := by rw [ENNReal.inv_mul_cancel hk0 hkt, one_mul]
  constructor
  · intro h
    have hh := ENNReal.mul_lt_mul_left
      (ENNReal.inv_ne_zero.mpr hkt)
      (ENNReal.inv_ne_top.mpr hk0) h
    simpa only [hcanc] using hh
  · intro h
    have hh := ENNReal.mul_lt_mul_left hk0 hkt h
    simpa only [mul_comm (C * S) k, mul_comm R k] using hh

 

theorem normalizedContLFPP_good_iff_affine
    (ξ : ℝ) (a a' : Ioi (0 : ℝ))
    {φ φ' : C(ℂ, ℝ)} {b c : ℂ} (hc : c ≠ 0)
    (k₀ : ℝ) (hφ : ∀ x, φ' x = φ (b + c * x) + k₀)
    (T : ℂ ≃ₜ ℂ) (hT : ∀ x, T x = b + c * x)
    (A E F : Set ℂ) (C : ℝ≥0∞) :
    C * LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a' φ') E F <
        (normalizedContLFPP ξ a' φ').aroundDist A E F ↔
      C * LQGMetric.Blueprint.setDist (normalizedContLFPP ξ a φ)
          (T '' E) (T '' F) <
        (normalizedContLFPP ξ a φ).aroundDist
          (T '' A) (T '' E) (T '' F) := by
  obtain ⟨hR, hS⟩ :=
    normalizedContLFPP_affine_costs ξ a a' hc k₀ hφ T hT A E F
  rw [hR, hS]
  have hκ : 0 < (a : ℝ) * Real.exp (ξ * k₀) /
      ((a' : ℝ) * ‖c‖) := by
    exact div_pos (mul_pos a.property (Real.exp_pos _))
      (mul_pos a'.property (norm_pos_iff.mpr hc))
  exact good_cost_iff_common_mul _ C _ _
    (ENNReal.ofReal_pos.mpr hκ).ne' ENNReal.ofReal_ne_top

end SupercriticalLQGUniqueness.B2.DG20Lim
