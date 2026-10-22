import HigherDimLQGContinuity.Improve.PowerThreshold

/-!
# One spare mesh power absorbs the cap index
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- The cap grid index is at most linear in `V`; the exponential scale can
pay for that denominator with two mesh powers. -/
theorem q11_exp_below_linear_denom {V z B : ℝ}
    (hV : 1 ≤ V) (hz : 0 < z)
    (hB : 2 + max 0 (-Real.log (z / 7)) ≤ B) :
    Real.exp (-(B * V)) * (3 * V + 4) ≤ z * Real.exp (-V) := by
  have hsmall := q11_exp_below_power hV
    (show 0 < z / 7 by positivity) hB
  have hlin : 3 * V + 4 ≤ 7 * Real.exp V := by
    have he := Real.add_one_le_exp V
    linarith
  have hnonneg : 0 ≤ 3 * V + 4 := by linarith
  have hstep := mul_le_mul hsmall hlin hnonneg
    (by positivity : 0 ≤ z / 7 * (Real.exp (-V)) ^ (2 : ℝ))
  have hpow : (Real.exp (-V)) ^ (2 : ℝ) * Real.exp V = Real.exp (-V) := by
    rw [Real.rpow_two, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have heq : (z / 7 * (Real.exp (-V)) ^ (2 : ℝ)) *
      (7 * Real.exp V) = z * Real.exp (-V) := by
    calc
      z / 7 * (Real.exp (-V) ^ (2 : ℝ)) * (7 * Real.exp V) =
          z * ((Real.exp (-V) ^ (2 : ℝ)) * Real.exp V) := by ring
      _ = z * Real.exp (-V) := by rw [hpow]
  exact hstep.trans_eq heq

end HigherDimLQGContinuity
