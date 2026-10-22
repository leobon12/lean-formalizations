import HigherDimLQGContinuity.Core.Interfaces

/-!
# Arithmetic for the active-site count

The deterministic consequence of comparison (4.19), with the constants of blueprint Part B.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-- The active-site bound from (4.19). -/
theorem active_sites_bound {m k : ℕ} {v cseed Q U₀ A₀ Cb gΔ ηloc cg cη : ℝ} (hv : 0 < v)
    (hcs : 0 < cseed) (hQ : 0 < Q) (_hU₀ : 0 < U₀) (hcg : 0 ≤ cg) (_hcη : 0 ≤ cη) (hcη1 : cη ≤ 1)
    (hCb : 0 ≤ Cb) (hA₀ : 0 ≤ A₀)
    (hgΔ : gΔ * U₀ ≤ cg * v * cseed * Q) (hη : ηloc ≤ cη * v * cseed * Q)
    (h419 : 12 * v * cseed * m * Q ≤ gΔ * U₀ + 2 * Cb * A₀ * k * Q + (m + 2 * k + 1) * ηloc) :
    (m : ℝ) ≤ (cg + 3 + 2 * Cb * A₀ / (v * cseed)) * (k + 1) := by
  have hx : 0 < v * cseed := mul_pos hv hcs
  have hq : 0 < v * cseed * Q := mul_pos hx hQ
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hcoeff : 0 ≤ (m : ℝ) + 2 * k + 1 := by positivity
  have hη' : ((m : ℝ) + 2 * k + 1) * ηloc ≤
      ((m : ℝ) + 2 * k + 1) * (v * cseed * Q) := by
    calc
      _ ≤ ((m : ℝ) + 2 * k + 1) * (cη * v * cseed * Q) :=
        mul_le_mul_of_nonneg_left hη hcoeff
      _ ≤ ((m : ℝ) + 2 * k + 1) * (v * cseed * Q) := by
        apply mul_le_mul_of_nonneg_left _ hcoeff
        nlinarith [mul_nonneg (sub_nonneg.mpr hcη1) (le_of_lt hq)]
  have hnum : 11 * (m : ℝ) * (v * cseed * Q) ≤
      (cg + 2 * k + 1) * (v * cseed * Q) + 2 * Cb * A₀ * k * Q := by
    nlinarith [hgΔ, hη', h419]
  have hbound : (cg + 2 * (k : ℝ) + 1) * (v * cseed * Q) +
      2 * Cb * A₀ * k * Q ≤
      ((cg + 3) * (k + 1) * (v * cseed) + 2 * Cb * A₀ * (k + 1)) * Q := by
    nlinarith [mul_nonneg hcg hk, mul_nonneg (mul_nonneg hCb hA₀) (le_of_lt hQ),
      mul_nonneg (by positivity : 0 ≤ cg + 1) (by positivity : 0 ≤ (k : ℝ) + 1)]
  have hmain : (m : ℝ) * (v * cseed) ≤
      (cg + 3 + 2 * Cb * A₀ / (v * cseed)) * (k + 1) * (v * cseed) := by
    apply (mul_le_mul_iff_of_pos_right hQ).mp
    have heq : (cg + 3 + 2 * Cb * A₀ / (v * cseed)) * (k + 1) *
        (v * cseed) * Q =
        ((cg + 3) * (k + 1) * (v * cseed) + 2 * Cb * A₀ * (k + 1)) * Q := by
      field_simp
    rw [heq]
    nlinarith [hnum, hbound, mul_nonneg hm (le_of_lt hq)]
  exact (mul_le_mul_iff_of_pos_right hx).mp hmain

end HigherDimLQGContinuity
