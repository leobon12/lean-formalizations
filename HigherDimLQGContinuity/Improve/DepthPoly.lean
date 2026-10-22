import HigherDimLQGContinuity.Core.Interfaces

/-!
# Absorbing fixed thresholds into a single polynomial depth
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- A fixed auxiliary depth threshold can be absorbed into the same
two-variable polynomial that controls Proposition 4.5. -/
theorem q11_poly_absorb_constant {Ap kp L : ℝ} (hL : 0 ≤ L) :
    ∃ A k : ℝ, 0 ≤ A ∧ 0 ≤ k ∧
      ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
        polyB Ap kp x y ≤ polyB A k x y ∧
        L ≤ polyB A k x y := by
  let A : ℝ := |Ap| + L
  let k : ℝ := max kp 0
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hk : 0 ≤ k := le_max_right _ _
  refine ⟨A, k, hA, hk, fun x y hx hy => ?_⟩
  let X : ℝ := 1 + x + y
  have hX : 1 ≤ X := by dsimp [X]; linarith
  have hpow0 : 0 ≤ X ^ kp := Real.rpow_nonneg (by linarith) _
  have hpowle : X ^ kp ≤ X ^ k :=
    Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _)
  have hpow1 : 1 ≤ X ^ k := Real.one_le_rpow hX hk
  constructor
  · change Ap * X ^ kp ≤ A * X ^ k
    calc
      Ap * X ^ kp ≤ |Ap| * X ^ kp :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hpow0
      _ ≤ |Ap| * X ^ k := mul_le_mul_of_nonneg_left hpowle (abs_nonneg _)
      _ ≤ A * X ^ k :=
        mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (by positivity)
  · change L ≤ A * X ^ k
    have hLA : L ≤ A := by dsimp [A]; linarith [abs_nonneg Ap]
    exact hLA.trans (le_mul_of_one_le_right hA hpow1)

/-- The logarithmic auxiliary depth of Step 1 fits the same fixed
polynomial as the forcing count depth. -/
theorem q11_poly_absorb_log_depth {Ap kp C : ℝ} (hC : 0 ≤ C) :
    ∃ A k : ℝ, 0 ≤ A ∧ 1 ≤ k ∧
      ∀ a v : ℝ, 0 < a → 0 < v →
        polyB Ap kp a⁻¹ v⁻¹ ≤ polyB A k a⁻¹ v⁻¹ ∧
        C * (1 + Real.log a⁻¹ + Real.log v⁻¹) ≤
          polyB A k a⁻¹ v⁻¹ := by
  let A : ℝ := |Ap| + C
  let k : ℝ := max kp 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hk : 1 ≤ k := le_max_right _ _
  refine ⟨A, k, hA, hk, fun a v ha hv => ?_⟩
  let X : ℝ := 1 + a⁻¹ + v⁻¹
  have hX : 1 ≤ X := by dsimp [X]; have := inv_pos.mpr ha; have := inv_pos.mpr hv; linarith
  have hpow0 : 0 ≤ X ^ kp := Real.rpow_nonneg (by linarith) _
  have hpowle : X ^ kp ≤ X ^ k :=
    Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _)
  have hXle : X ≤ X ^ k := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hX hk : X ^ (1 : ℝ) ≤ X ^ k)
  have hlog : 1 + Real.log a⁻¹ + Real.log v⁻¹ ≤ X := by
    dsimp [X]
    have haLog := Real.log_le_self (inv_pos.mpr ha).le
    have hvLog := Real.log_le_self (inv_pos.mpr hv).le
    linarith
  constructor
  · change Ap * X ^ kp ≤ A * X ^ k
    calc
      Ap * X ^ kp ≤ |Ap| * X ^ kp :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hpow0
      _ ≤ |Ap| * X ^ k := mul_le_mul_of_nonneg_left hpowle (abs_nonneg _)
      _ ≤ A * X ^ k :=
        mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (by positivity)
  · change C * (1 + Real.log a⁻¹ + Real.log v⁻¹) ≤ A * X ^ k
    calc
      C * (1 + Real.log a⁻¹ + Real.log v⁻¹) ≤ C * X :=
        mul_le_mul_of_nonneg_left hlog hC
      _ ≤ C * X ^ k := mul_le_mul_of_nonneg_left hXle hC
      _ ≤ A * X ^ k :=
        mul_le_mul_of_nonneg_right (by dsimp [A]; linarith [abs_nonneg Ap]) (by positivity)

end HigherDimLQGContinuity
