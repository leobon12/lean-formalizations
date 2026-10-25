import SupercriticalLQGUniqueness.B2.DG20Lim.NormalizedAroundFourPoint

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem normalizedContLFPP_aroundDist_lt_of_four_point_crossLe
    (A : EuclideanAnnulus) (ξ : ℝ) (φ : C(ℂ, ℝ))
    (a : Ioi (0 : ℝ)) (z w : Fin 4 → ℂ)
    (hz : ∀ j, z j ∈ B2.Strong.cfgSet₁ A j)
    (hw : ∀ j, w j ∈ B2.Strong.cfgSet₂ A j)
    (M : ℝ) (hM : 0 ≤ M)
    (hcross : ∀ j : Fin 4,
      ENNReal.ofReal ((a : ℝ)⁻¹) *
        crossLenIn ξ φ (B2.Strong.cfgOpens A j : Set ℂ)
          {z j} {w j} ≤ ENNReal.ofReal M) :
    (normalizedContLFPP ξ a φ).aroundDist A.toSet
      A.innerBoundary A.outerBoundary < ENNReal.ofReal (6 * (M + 1)) := by
  let k : ℝ≥0∞ := ENNReal.ofReal (a : ℝ)
  let c : ℝ≥0∞ := ENNReal.ofReal ((a : ℝ)⁻¹)
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr a.property).ne'
  have hkt : k ≠ ∞ := ENNReal.ofReal_ne_top
  have hkc : k * c = 1 := by
    dsimp [k, c]
    rw [← ENNReal.ofReal_mul a.property.le,
      mul_inv_cancel₀ a.property.ne', ENNReal.ofReal_one]
  have hM1 : 0 < M + 1 := by linarith
  let b : ℝ≥0∞ := k * ENNReal.ofReal (M + 1)
  have hb0 : b ≠ 0 :=
    mul_ne_zero hk0 (ENNReal.ofReal_pos.mpr hM1).ne'
  have hbt : b ≠ ∞ :=
    ENNReal.mul_ne_top hkt ENNReal.ofReal_ne_top
  have hraw (j : Fin 4) :
      crossLenIn ξ φ (B2.Strong.cfgOpens A j : Set ℂ)
        {z j} {w j} < b := by
    have hbase : crossLenIn ξ φ (B2.Strong.cfgOpens A j : Set ℂ)
        {z j} {w j} ≤ k * ENNReal.ofReal M := by
      calc
        _ = (k * c) * crossLenIn ξ φ (B2.Strong.cfgOpens A j : Set ℂ)
            {z j} {w j} := by rw [hkc, one_mul]
        _ = k * (c * crossLenIn ξ φ (B2.Strong.cfgOpens A j : Set ℂ)
            {z j} {w j}) := by rw [mul_assoc]
        _ ≤ k * ENNReal.ofReal M :=
          mul_le_mul_of_nonneg_left (hcross j) zero_le
    apply hbase.trans_lt
    simpa only [b, mul_comm] using
      (ENNReal.mul_lt_mul_iff_left hk0 hkt).2
        ((ENNReal.ofReal_lt_ofReal_iff hM1).2 (by linarith))
  have hbudget : b + b + b + b < 5 * b := by
    have hsum : b + b + b + b = (4 : ℝ≥0∞) * b := by ring
    rw [hsum]
    simpa only [mul_comm] using
      (ENNReal.mul_lt_mul_iff_right hb0 hbt).2
        (by norm_num : (4 : ℝ≥0∞) < 5)
  have hscaled : c * (5 * b) < ENNReal.ofReal (6 * (M + 1)) := by
    have hcb : c * b = ENNReal.ofReal (M + 1) := by
      dsimp [b]
      calc
        c * (k * ENNReal.ofReal (M + 1)) = (k * c) * ENNReal.ofReal (M + 1) := by ac_rfl
        _ = ENNReal.ofReal (M + 1) := by rw [hkc, one_mul]
    calc
      c * (5 * b) = 5 * ENNReal.ofReal (M + 1) := by rw [mul_left_comm, hcb]
      _ = ENNReal.ofReal (5 * (M + 1)) := by
        have h5 : (5 : ℝ≥0∞) = ENNReal.ofReal (5 : ℝ) := by norm_num
        rw [h5]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
      _ < ENNReal.ofReal (6 * (M + 1)) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 6 * (M + 1))).2
          (by nlinarith)
  exact normalizedContLFPP_aroundDist_lt_of_four_point_crossLen
    A ξ φ a z w hz hw b b b b (5 * b) _
    (hraw 0) (hraw 1) (hraw 2) (hraw 3) hbudget hscaled

end SupercriticalLQGUniqueness.B2.DG20Lim
