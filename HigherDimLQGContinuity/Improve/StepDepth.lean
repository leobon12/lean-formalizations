import HigherDimLQGContinuity.Improve.DepthPoly
import HigherDimLQGContinuity.ForcingCount.Poly

/-!
# One polynomial depth for the deterministic thresholds
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- A fixed threshold and the logarithmic parameter cost fit in one depth
polynomial chosen before the lower endpoint and tolerance. -/
theorem q11_step_depth {Ap kp C a v : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (hv : 0 < v) :
    let A := |Ap| + C + 2
    let k := max kp 1
    let V := polyB A k a⁻¹ v⁻¹
    1 ≤ V ∧ polyB Ap kp a⁻¹ v⁻¹ + C + Real.log v⁻¹ ≤ V := by
  let X : ℝ := 1 + a⁻¹ + v⁻¹
  have hX : 1 ≤ X := by
    dsimp [X]
    have := inv_pos.mpr ha
    have := inv_pos.mpr hv
    linarith
  have hk : 1 ≤ max kp 1 := le_max_right _ _
  have hpow : 1 ≤ X ^ max kp 1 := Real.one_le_rpow hX (by linarith)
  have hXpow : X ≤ X ^ max kp 1 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hX hk : X ^ (1 : ℝ) ≤ X ^ max kp 1)
  have hkpow : X ^ kp ≤ X ^ max kp 1 :=
    Real.rpow_le_rpow_of_exponent_le hX (le_max_left _ _)
  have hlog : Real.log v⁻¹ ≤ v⁻¹ := Real.log_le_self (inv_pos.mpr hv).le
  have hvX : v⁻¹ ≤ X := by dsimp [X]; have := inv_pos.mpr ha; linarith
  have hAp0 : 0 ≤ X ^ kp := Real.rpow_nonneg (by linarith) _
  have hAp : Ap * X ^ kp ≤ |Ap| * X ^ max kp 1 := by
    calc
      Ap * X ^ kp ≤ |Ap| * X ^ kp :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hAp0
      _ ≤ |Ap| * X ^ max kp 1 :=
        mul_le_mul_of_nonneg_left hkpow (abs_nonneg _)
  have hClog : C + Real.log v⁻¹ ≤ (C + 1) * X ^ max kp 1 := by
    have hCsmall : C ≤ C * X ^ max kp 1 :=
      le_mul_of_one_le_right hC hpow
    have hvsmall : Real.log v⁻¹ ≤ X ^ max kp 1 :=
      hlog.trans (hvX.trans hXpow)
    nlinarith only [hCsmall, hvsmall]
  have hV : 1 ≤ (|Ap| + C + 2) * X ^ max kp 1 := by
    have hA : 1 ≤ |Ap| + C + 2 := by linarith [abs_nonneg Ap]
    nlinarith only [hA, hpow, abs_nonneg Ap, hC]
  change 1 ≤ (|Ap| + C + 2) * X ^ max kp 1 ∧
    Ap * X ^ kp + C + Real.log v⁻¹ ≤
      (|Ap| + C + 2) * X ^ max kp 1
  constructor
  · exact hV
  · nlinarith only [hAp, hClog, hpow]

/-- The depth needed by Proposition 4.5 and the seed-certificate lower bound
can be paid simultaneously by a polynomial fixed before `a` and `v`. -/
theorem q11_step_depth_site {A45 k45 Ap kp C a v : ℝ}
    (hC : 0 ≤ C) (ha : 0 < a) (hv : 0 < v) :
    let A := |A45| + |Ap| + C + 3
    let k := max (max k45 kp) 1
    let V := polyB A k a⁻¹ v⁻¹
    1 ≤ V ∧ a⁻¹ ≤ V ∧ v⁻¹ ≤ V ∧
      polyB Ap kp 0 v⁻¹ ≤ V ∧ polyB A45 k45 a⁻¹ v⁻¹ ≤ V ∧
      polyB A45 k45 a⁻¹ v⁻¹ + polyB Ap kp 0 v⁻¹ +
        C + Real.log v⁻¹ ≤ V := by
  let X : ℝ := 1 + a⁻¹ + v⁻¹
  let k : ℝ := max (max k45 kp) 1
  have hX : 1 ≤ X := by
    dsimp [X]
    have := inv_pos.mpr ha
    have := inv_pos.mpr hv
    linarith
  have hk45 : k45 ≤ k := (le_max_left _ _).trans (le_max_left _ _)
  have hkp : kp ≤ k := (le_max_right _ _).trans (le_max_left _ _)
  have hk1 : 1 ≤ k := le_max_right _ _
  have hk0 : 0 ≤ k := by linarith
  have hpow : 1 ≤ X ^ k := Real.one_le_rpow hX hk0
  have hXpow : X ≤ X ^ k := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hX hk1 : X ^ (1 : ℝ) ≤ X ^ k)
  have h45pow : X ^ k45 ≤ X ^ k :=
    Real.rpow_le_rpow_of_exponent_le hX hk45
  have hppow : X ^ (max kp 0) ≤ X ^ k :=
    Real.rpow_le_rpow_of_exponent_le hX
      (max_le hkp hk0)
  have h45 : polyB A45 k45 a⁻¹ v⁻¹ ≤ |A45| * X ^ k := by
    change A45 * X ^ k45 ≤ |A45| * X ^ k
    calc
      A45 * X ^ k45 ≤ |A45| * X ^ k45 :=
        mul_le_mul_of_nonneg_right (le_abs_self _)
          (Real.rpow_nonneg (by linarith) _)
      _ ≤ |A45| * X ^ k := mul_le_mul_of_nonneg_left h45pow (abs_nonneg _)
  have hp : polyB Ap kp 0 v⁻¹ ≤ |Ap| * X ^ k :=
    (q9_polyB_le ha hv).trans
      (mul_le_mul_of_nonneg_left hppow (abs_nonneg _))
  have hlog : Real.log v⁻¹ ≤ X ^ k := by
    calc
      Real.log v⁻¹ ≤ v⁻¹ := Real.log_le_self (inv_pos.mpr hv).le
      _ ≤ X := by dsimp [X]; have := inv_pos.mpr ha; linarith
      _ ≤ X ^ k := hXpow
  have hCsmall : C ≤ C * X ^ k := le_mul_of_one_le_right hC hpow
  have hV : 1 ≤ (|A45| + |Ap| + C + 3) * X ^ k := by
    have hA : 1 ≤ |A45| + |Ap| + C + 3 := by
      linarith [abs_nonneg A45, abs_nonneg Ap]
    nlinarith only [hA, hpow, abs_nonneg A45, abs_nonneg Ap, hC]
  change 1 ≤ (|A45| + |Ap| + C + 3) * X ^ k ∧
    a⁻¹ ≤ (|A45| + |Ap| + C + 3) * X ^ k ∧
    v⁻¹ ≤ (|A45| + |Ap| + C + 3) * X ^ k ∧
    polyB Ap kp 0 v⁻¹ ≤ (|A45| + |Ap| + C + 3) * X ^ k ∧
    polyB A45 k45 a⁻¹ v⁻¹ ≤ (|A45| + |Ap| + C + 3) * X ^ k ∧
    polyB A45 k45 a⁻¹ v⁻¹ + polyB Ap kp 0 v⁻¹ + C +
      Real.log v⁻¹ ≤ (|A45| + |Ap| + C + 3) * X ^ k
  refine ⟨hV, ?_, ?_, ?_, ?_, ?_⟩
  · have haX : a⁻¹ ≤ X := by dsimp [X]; have := inv_pos.mpr hv; linarith
    nlinarith only [haX, hXpow, hpow, abs_nonneg A45, abs_nonneg Ap, hC]
  · have hvX : v⁻¹ ≤ X := by dsimp [X]; have := inv_pos.mpr ha; linarith
    nlinarith only [hvX, hXpow, hpow, abs_nonneg A45, abs_nonneg Ap, hC]
  · nlinarith only [hp, hpow, abs_nonneg A45, abs_nonneg Ap, hC]
  · nlinarith only [h45, hpow, abs_nonneg A45, abs_nonneg Ap, hC]
  · nlinarith only [h45, hp, hlog, hCsmall, hpow]

end HigherDimLQGContinuity
