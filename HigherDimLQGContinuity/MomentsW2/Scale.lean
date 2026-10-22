import HigherDimLQGContinuity.MomentsW2.MomentCalc
import HigherDimLQGMetric.DGZ.Chain

/-!
# Dyadic scale arithmetic for W2

The chosen bad-cluster diameter is linear in the coarse scale. This is enough
for an arbitrary prescribed inverse moment order and simplifies the Peierls term.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

/-- Exact normalized crossing threshold in exponential notation. -/
theorem w2_threshold_eq (c A b : ℝ) (m : ℕ) :
    c * (2 : ℝ)⁻¹ ^ m / (4 * Real.exp (A * m * Real.log 2) *
      (2 : ℝ) ^ (b ^ 2 * m / 2)) =
    (c / 4) * (2 : ℝ) ^ (-((A + 1 + b ^ 2 / 2) * m)) := by
  rw [show (2 : ℝ)⁻¹ ^ m = (2 : ℝ) ^ (-(m : ℝ)) by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, inv_pow]]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  field_simp
  calc
    c * Real.exp (-(Real.log 2 * (m : ℝ))) =
        c * (Real.exp (Real.log 2 * m * A) * Real.exp (Real.log 2 * m * b ^ 2 / 2) *
          Real.exp (-(Real.log 2 * m * (2 * (A + 1) + b ^ 2) / 2))) := by
            congr 1
            rw [mul_assoc, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
    _ = _ := by ring

/-- For all sufficiently fine scales, a cluster of diameter `2Lm` fits inside the shell. -/
theorem w2_exists_geom_start {w : ℝ} (hw : 0 < w) (L : ℕ) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      (2 : ℝ)⁻¹ ^ m ≤ 1 / 2 ∧
      ((2 * L * m : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ m + 8 * (2 : ℝ)⁻¹ ^ m ≤ w := by
  let m₀ : ℕ := max 20 ⌈(2 * (L : ℝ) + 8) / (1000 * w)⌉₊
  refine ⟨m₀, by dsimp [m₀]; omega, ?_⟩
  intro m hm
  have hm20 : 20 ≤ m := (le_max_left _ _).trans hm
  have hm1 : 1 ≤ m := by omega
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hs : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  have hs2 : (2 : ℝ)⁻¹ ^ m ≤ 1 / 2 := by
    have hm1' : 1 ≤ m := hm1
    calc
      (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ (1 : ℕ) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1'
      _ = 1 / 2 := by norm_num
  refine ⟨hs2, ?_⟩
  have hpow : 1000 * (m : ℝ) ^ 2 ≤ (2 : ℝ) ^ m := by
    exact_mod_cast HigherDimLQGMetric.DGZ.thousand_mul_sq_le_two_pow hm20
  have hceil : (2 * (L : ℝ) + 8) / (1000 * w) ≤ m := by
    have h1 := Nat.le_ceil ((2 * (L : ℝ) + 8) / (1000 * w))
    have h2 : ⌈(2 * (L : ℝ) + 8) / (1000 * w)⌉₊ ≤ m := (le_max_right _ _).trans hm
    exact h1.trans (by exact_mod_cast h2)
  have hL : 2 * (L : ℝ) + 8 ≤ 1000 * w * m := by
    have hL' : 2 * (L : ℝ) + 8 ≤ (m : ℝ) * (1000 * w) :=
      (div_le_iff₀ (by positivity : 0 < 1000 * w)).1 hceil
    nlinarith only [hL']
  have hnum : ((2 * L * m : ℕ) : ℝ) + 8 ≤ w * (2 : ℝ) ^ m := by
    have h1 : ((2 * L * m : ℕ) : ℝ) + 8 ≤ (2 * (L : ℝ) + 8) * m := by
      push_cast
      nlinarith only [hmreal]
    have h2 : (2 * (L : ℝ) + 8) * m ≤ 1000 * w * m ^ 2 := by
      nlinarith only [hL, hmreal, hw]
    have h3 : 1000 * w * m ^ 2 ≤ w * (2 : ℝ) ^ m :=
      by simpa only [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_of_nonneg_left hpow hw.le)
    linarith only [h1, h2, h3]
  have hinv : (2 : ℝ)⁻¹ ^ m * (2 : ℝ) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
  have hscaled := mul_le_mul_of_nonneg_left hnum hs.le
  calc
    ((2 * L * m : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ m + 8 * (2 : ℝ)⁻¹ ^ m =
        (2 : ℝ)⁻¹ ^ m * (((2 * L * m : ℕ) : ℝ) + 8) := by ring
    _ ≤ (2 : ℝ)⁻¹ ^ m * (w * (2 : ℝ) ^ m) := hscaled
    _ = w := by calc
      (2 : ℝ)⁻¹ ^ m * (w * (2 : ℝ) ^ m) = w * ((2 : ℝ)⁻¹ ^ m * (2 : ℝ) ^ m) := by ring
      _ = w := by rw [hinv, mul_one]

/-- An integer cover of the shell region has at most exponential volume growth. -/
theorem w2_peierls_le {r₁ : ℝ} {N L d m : ℕ}
    (hN : (N : ℝ) ≤ r₁ * (2 : ℝ) ^ m + 1) :
    (2 * (N : ℝ≥0∞) + 1) ^ d * 2⁻¹ ^ ((2 * L * m) / 2) ≤
      ENNReal.ofReal ((2 * r₁ + 3) ^ d * (2 : ℝ) ^ (((d : ℝ) - L) * m)) := by
  rw [show (2 * L * m) / 2 = L * m by
    rw [mul_assoc, Nat.mul_div_cancel_left]
    norm_num]
  rw [HigherDimLFPP.L33.box_mul_pow_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have hbase : 2 * (N : ℝ) + 1 ≤ (2 * r₁ + 3) * (2 : ℝ) ^ m := by
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    nlinarith only [hN, hpow]
  have hp1 : (2 * (N : ℝ) + 1) ^ d ≤ ((2 * r₁ + 3) * (2 : ℝ) ^ m) ^ d :=
    pow_le_pow_left₀ (by positivity) hbase d
  have he : ((2 * r₁ + 3) * (2 : ℝ) ^ m) ^ d * (2⁻¹ : ℝ) ^ (L * m) =
      (2 * r₁ + 3) ^ d * (2 : ℝ) ^ (((d : ℝ) - L) * m) := by
    have htwo : ((2 : ℝ) ^ m) ^ d = Real.exp ((m * d : ℕ) * Real.log 2) := by
      rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring_nf
    have hinv : (2⁻¹ : ℝ) ^ (L * m) = Real.exp (-(L * m : ℕ) * Real.log 2) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Real.log_inv]
      congr 1
      push_cast
      ring_nf
    rw [mul_pow, htwo, hinv, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      (2 * r₁ + 3) ^ d * Real.exp ((m * d : ℕ) * Real.log 2) *
          Real.exp (-(L * m : ℕ) * Real.log 2) =
        (2 * r₁ + 3) ^ d * Real.exp (((m * d : ℕ) : ℝ) * Real.log 2 -
          ((L * m : ℕ) : ℝ) * Real.log 2) := by rw [mul_assoc, ← Real.exp_add]; congr 1; ring_nf
      _ = _ := by congr 1; congr 1; push_cast; ring_nf
  calc
    (2 * (N : ℝ) + 1) ^ d * (2⁻¹ : ℝ) ^ (L * m)
        ≤ ((2 * r₁ + 3) * (2 : ℝ) ^ m) ^ d * (2⁻¹ : ℝ) ^ (L * m) :=
          mul_le_mul_of_nonneg_right hp1 (by positivity)
    _ = _ := he

/-- Bounds for the integer box containing every potentially bad cell. -/
theorem w2_ceil_bounds {r₁ : ℝ} (hr₁ : 0 ≤ r₁) (m : ℕ) :
    let N := ⌈r₁ / ((2 : ℝ)⁻¹ ^ m)⌉₊
    r₁ / ((2 : ℝ)⁻¹ ^ m) ≤ N ∧
      (N : ℝ) ≤ r₁ * (2 : ℝ) ^ m + 1 := by
  intro N
  have hs : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  have hrec : (2 : ℝ)⁻¹ ^ m * (2 : ℝ) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
  have hquot : r₁ / ((2 : ℝ)⁻¹ ^ m) = r₁ * (2 : ℝ) ^ m := by
    rw [div_eq_iff hs.ne']
    linear_combination r₁ * hrec.symm
  constructor
  · exact Nat.le_ceil _
  · have hlt : (N : ℝ) < r₁ / ((2 : ℝ)⁻¹ ^ m) + 1 := by
      exact Nat.ceil_lt_add_one (div_nonneg hr₁ hs.le)
    rw [hquot] at hlt
    exact hlt.le

end HigherDimLQGContinuity
