import HigherDimLQGMetric.Thm16.RatioAlgebra

/-! Cancel the common random Weyl factor in the two Prop 4.2 inequalities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace HigherDimLQGMetric

theorem l9c_ratio_upper_algebra {a b c t η M C r : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (ht : 0 < t) (hη : 0 < η) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (h : ENNReal.ofReal a⁻¹ * ENNReal.ofReal (r * t * b * η) ≤
      ENNReal.ofReal C * ENNReal.ofReal (c * t * M)) :
    r * b / a ≤ (C * M / η) * c := by
  have hreal : a⁻¹ * (r * t * b * η) ≤ C * (c * t * M) := by
    have h' : ENNReal.ofReal (a⁻¹ * (r * t * b * η)) ≤
        ENNReal.ofReal (C * (c * t * M)) := by
      simpa only [ENNReal.ofReal_mul (inv_pos.mpr ha).le,
        ENNReal.ofReal_mul hC] using h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h'
  have hcancel : a⁻¹ * r * b * η ≤ C * c * M :=
    (mul_le_mul_iff_of_pos_right ht).1 (by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hreal)
  have hdiv : a⁻¹ * r * b ≤ (C * c * M) / η :=
    (le_div_iff₀ hη).2 (by simpa only [mul_assoc] using hcancel)
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

theorem l9c_ratio_lower_algebra {a b c t η M C r : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) (hη : 0 < η) (hM : 0 ≤ M) (hC : 0 ≤ C) (hr : 0 < r)
    (h : ENNReal.ofReal (c * t * η) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal a⁻¹ * ENNReal.ofReal (r * t * b * M))) :
    c ≤ (C * M / η) * (r * b / a) := by
  have hreal : c * t * η ≤ C * (a⁻¹ * (r * t * b * M)) := by
    have h' : ENNReal.ofReal (c * t * η) ≤
        ENNReal.ofReal (C * (a⁻¹ * (r * t * b * M))) := by
      simpa only [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (inv_pos.mpr ha).le] using h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h'
  have hcancel : c * η ≤ C * a⁻¹ * r * b * M :=
    (mul_le_mul_iff_of_pos_right ht).1 (by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hreal)
  have hdiv : c ≤ (C * a⁻¹ * r * b * M) / η :=
    (le_div_iff₀ hη).2 (by simpa only [mul_assoc] using hcancel)
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

end HigherDimLQGMetric
