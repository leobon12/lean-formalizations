import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field

/-! Deterministic cancellation of three normalization ratios. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGMetric

def l9c_ratio (a : ℝ → ℝ) (ε r : ℝ) : ℝ :=
  r * a (ε / r) / a ε

private theorem l9c_ratio_mul (a : ℝ → ℝ) {ε r s : ℝ}
    (haε : a ε ≠ 0) (haεr : a (ε / r) ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    l9c_ratio a ε r * l9c_ratio a (ε / r) s =
      l9c_ratio a ε (r * s) := by
  unfold l9c_ratio
  have heq : ε / r / s = ε / (r * s) := by field_simp
  rw [heq]
  field_simp

/-- The pointwise eventual form of (4.14) implies approximate multiplicativity.
The scale `ε` may depend on the fixed pair `(r,s)`; the constant does not. -/
theorem l9c_approxMul_of_ratio {a c : ℝ → ℝ}
    (ha : ∀ ε : ℝ, 0 < ε → 0 < a ε)
    (hc : ∀ r : ℝ, 0 < r → 0 < c r)
    {K : ℝ} (hK : 1 ≤ K)
    (hR : ∀ r : ℝ, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      K⁻¹ * c r ≤ l9c_ratio a ε r ∧
        l9c_ratio a ε r ≤ K * c r) :
    ∀ r s : ℝ, 0 < r → 0 < s →
      c r * c s ≤ K ^ 3 * c (r * s) ∧
        c (r * s) ≤ K ^ 3 * (c r * c s) := by
  intro r s hr hs
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hεs := eventually_nhdsGT_zero_mul_left (inv_pos.mpr hr) (hR s hs)
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, ⟨⟨hεpos, hxr⟩, hys⟩, hzs⟩ :=
    (hε.and (hR r hr) |>.and hεs |>.and (hR (r * s) (mul_pos hr hs))).exists
  have hys' : K⁻¹ * c s ≤ l9c_ratio a (ε / r) s ∧
      l9c_ratio a (ε / r) s ≤ K * c s := by
    simpa only [inv_mul_eq_div] using hys
  let x := l9c_ratio a ε r
  let y := l9c_ratio a (ε / r) s
  let z := l9c_ratio a ε (r * s)
  have hxy : x * y = z :=
    l9c_ratio_mul a (ha ε hεpos).ne'
      (ha (ε / r) (div_pos hεpos hr)).ne' hr.ne' hs.ne'
  have hxpos : 0 < x := lt_of_lt_of_le (mul_pos (inv_pos.mpr hKpos) (hc r hr)) hxr.1
  have hypos : 0 < y := lt_of_lt_of_le (mul_pos (inv_pos.mpr hKpos) (hc s hs)) hys'.1
  have hzpos : 0 < z := lt_of_lt_of_le
    (mul_pos (inv_pos.mpr hKpos) (hc (r * s) (mul_pos hr hs))) hzs.1
  have hcr : c r ≤ K * x := by
    have h := mul_le_mul_of_nonneg_left hxr.1 hKpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hKpos.ne', one_mul] using h
  have hcs : c s ≤ K * y := by
    have h := mul_le_mul_of_nonneg_left hys'.1 hKpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hKpos.ne', one_mul] using h
  have hcrs : c (r * s) ≤ K * z := by
    have h := mul_le_mul_of_nonneg_left hzs.1 hKpos.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hKpos.ne', one_mul] using h
  constructor
  · calc
      c r * c s ≤ (K * x) * (K * y) :=
        mul_le_mul hcr hcs (hc s hs).le (mul_nonneg hKpos.le hxpos.le)
      _ = K ^ 2 * z := by rw [← hxy]; ring
      _ ≤ K ^ 2 * (K * c (r * s)) :=
        mul_le_mul_of_nonneg_left hzs.2 (sq_nonneg K)
      _ = K ^ 3 * c (r * s) := by ring
  · calc
      c (r * s) ≤ K * z := hcrs
      _ = K * (x * y) := by rw [hxy]
      _ ≤ K * ((K * c r) * (K * c s)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hxr.2 hys'.2 hypos.le
            (mul_nonneg hKpos.le (hc r hr).le)) hKpos.le
      _ = K ^ 3 * (c r * c s) := by ring

end HigherDimLQGMetric
