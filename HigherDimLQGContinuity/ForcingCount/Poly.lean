import HigherDimLQGContinuity.Core.Interfaces

/-!
# The depth polynomial of Proposition 4.5 and the counting arithmetic

Packet Q9 (real arithmetic). Part B `b:prop45`: the four depth conditions of `Prop45OfCounts` (with
`C_J = 4 max(C_cat, 1) J'`, `C_KJ = 4 K₁ J'`, `J' = max(J, 1)`, `K₁ ≤ C₁ v⁻¹ θ⁻¹`, and the Cameron–Martin level
`M₀ = max(a⁻¹ P_v², 1)`, `P_v = max(polyB A_p k_p 0 v⁻¹, 0)`) are implied by `ℓ ≥ polyB A₄₅ k₄₅ a⁻¹ v⁻¹` for constants
`A₄₅, k₄₅` depending only on the fixed data (`q9_depth_poly`), because `log J, log θ⁻¹ ≤ polyB A_p k_p 0 v⁻¹`
(site-certificate part (i)) and `log v⁻¹ ≤ v⁻¹`. The counting bounds `(k+1)(Y+1)^k ≤ (4W)^k` for `0 ≤ Y ≤ W`,
`1 ≤ W` (`q9_count_arith`) convert the library's small-subset count into the interface's forms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGContinuity

/-- `(k + 1)(Y + 1)^k ≤ (4W)^k` for `0 ≤ Y ≤ W`, `1 ≤ W`. -/
theorem q9_count_arith (k : ℕ) {Y W : ℝ} (hY : 0 ≤ Y) (hYW : Y ≤ W) (hW : 1 ≤ W) :
    ((k : ℝ) + 1) * (Y + 1) ^ k ≤ (4 * W) ^ k := by
  have h1 : Y + 1 ≤ 2 * W := by linarith
  have h2 : ((k : ℝ) + 1) ≤ 2 ^ k := by
    have := Nat.lt_two_pow_self (n := k)
    exact_mod_cast this
  calc ((k : ℝ) + 1) * (Y + 1) ^ k ≤ 2 ^ k * (2 * W) ^ k := by
        apply mul_le_mul h2 (pow_le_pow_left₀ (by linarith) h1 k) (by positivity) (by positivity)
    _ = (4 * W) ^ k := by rw [← mul_pow]; congr 1; ring

theorem q9_rpow_le_of_le_exp {X j k : ℝ} (hX : 1 ≤ X) (hj : j ≤ k) : X ^ j ≤ X ^ k :=
  Real.rpow_le_rpow_of_exponent_le hX hj

/-- `polyB A_p k_p 0 v⁻¹ ≤ |A_p| X^{max(k_p, 0)}` for `X = 1 + a⁻¹ + v⁻¹`. -/
theorem q9_polyB_le {Ap kp a v : ℝ} (ha : 0 < a) (hv : 0 < v) :
    polyB Ap kp 0 v⁻¹ ≤ |Ap| * (1 + a⁻¹ + v⁻¹) ^ (max kp 0) := by
  unfold polyB
  have hb1 : 1 ≤ 1 + 0 + v⁻¹ := by have := inv_pos.2 hv; linarith
  have hX : 1 + 0 + v⁻¹ ≤ 1 + a⁻¹ + v⁻¹ := by have := inv_pos.2 ha; linarith
  have hpow : (1 + 0 + v⁻¹) ^ kp ≤ (1 + a⁻¹ + v⁻¹) ^ (max kp 0) := by
    rcases le_total 0 kp with hk | hk
    · rw [max_eq_left hk]
      exact Real.rpow_le_rpow (by linarith) hX hk
    · rw [max_eq_right hk, Real.rpow_zero]
      exact Real.rpow_le_one_of_one_le_of_nonpos hb1 hk
  have hpos : 0 ≤ (1 + 0 + v⁻¹) ^ kp := Real.rpow_nonneg (by linarith) _
  calc Ap * (1 + 0 + v⁻¹) ^ kp ≤ |Ap| * (1 + 0 + v⁻¹) ^ kp :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hpos
    _ ≤ |Ap| * (1 + a⁻¹ + v⁻¹) ^ (max kp 0) := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)

/-- **The depth polynomial.** -/
theorem q9_depth_poly {κ D₀ Ccat C₁ Ap kp : ℝ} {k : ℕ} (hκ : 0 < κ) (hD₀ : 0 < D₀) (hk : 1 ≤ k)
    (hC₁ : 1 ≤ C₁) :
    ∃ A₄₅ k₄₅ : ℝ, ∀ a v J θ K₁ ℓ : ℝ, 0 < a → 0 < v → v ≤ 1 → 0 ≤ J →
      Real.log J ≤ polyB Ap kp 0 v⁻¹ → 0 < θ → Real.exp (-polyB Ap kp 0 v⁻¹) ≤ θ → θ < 1 →
      1 ≤ K₁ → K₁ ≤ C₁ * v⁻¹ * θ⁻¹ → polyB A₄₅ k₄₅ a⁻¹ v⁻¹ ≤ ℓ →
      max (max (Real.log (4 * max Ccat 1 * max J 1) / D₀)
        (4 * (2 * Real.log k + Real.log (4 * K₁ * max J 1) + 1) / (κ / 2)))
        (max (64 * k * D₀ * (max (a⁻¹ * max (polyB Ap kp 0 v⁻¹) 0 * max (polyB Ap kp 0 v⁻¹) 0) 1) ^ 2 /
          ((κ / 2) ^ 2)) (2 * Real.log k)) ≤ ℓ := by
  set k' := max kp 0 with hk'
  have hk'0 : 0 ≤ k' := le_max_right _ _
  set k₄₅ := 4 * k' + 2 with hk45
  set c₁ := Real.log 4 + Real.log (max Ccat 1) with hc₁
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  have hc₁0 : 0 ≤ c₁ := add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (le_max_right _ _))
  set c₂ := 2 * Real.log k + Real.log 4 + Real.log C₁ + 1 with hc₂
  have hc₂0 : 0 ≤ c₂ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    have := Real.log_nonneg hC₁
    linarith
  refine ⟨(c₁ + |Ap|) / D₀ + 8 / κ * (c₂ + 1 + 2 * |Ap|) + 256 * k * D₀ / κ ^ 2 * (1 + Ap ^ 2) ^ 2 +
    2 * Real.log k, k₄₅, ?_⟩
  intro a v J θ K₁ ℓ ha hv hv1 hJ hlogJ hθ hθl hθ1 hK₁ hK₁le hℓ
  set X := 1 + a⁻¹ + v⁻¹ with hXdef
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have hvi : 0 < v⁻¹ := inv_pos.2 hv
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hXk : ∀ j : ℝ, j ≤ k₄₅ → X ^ j ≤ X ^ k₄₅ := fun j hj => q9_rpow_le_of_le_exp hX1 hj
  have hXpos : ∀ j : ℝ, 0 < X ^ j := fun j => Real.rpow_pos_of_pos hX0 j
  have hX45 : 1 ≤ X ^ k₄₅ := Real.one_le_rpow hX1 (by positivity)
  set P := polyB Ap kp 0 v⁻¹ with hPdef
  set Pv := max P 0 with hPv
  have hPv0 : 0 ≤ Pv := le_max_right _ _
  have hPvle : Pv ≤ |Ap| * X ^ k' := max_le (q9_polyB_le ha hv) (by positivity)
  have hXk' : X ^ k' ≤ X ^ k₄₅ := hXk k' (by linarith)
  -- `log J' ≤ Pv`
  have hlogJ' : Real.log (max J 1) ≤ Pv := by
    rcases le_total J 1 with hJ1 | hJ1
    · rw [max_eq_right hJ1, Real.log_one]
      exact hPv0
    · rw [max_eq_left hJ1]
      exact hlogJ.trans (le_max_left _ _)
  have hJ'1 : 1 ≤ max J 1 := le_max_right _ _
  -- `log θ⁻¹ ≤ Pv`
  have hlogθ : Real.log θ⁻¹ ≤ Pv := by
    have h1 : -P ≤ Real.log θ := by
      have := Real.log_le_log (Real.exp_pos _) hθl
      rwa [Real.log_exp] at this
    rw [Real.log_inv]
    exact (neg_le.1 h1).trans (le_max_left _ _)
  have hlogθ0 : 0 ≤ Real.log θ⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hθ, hθ1.le⟩)
  -- `log K₁ ≤ log C₁ + X + Pv`
  have hlogK₁ : Real.log K₁ ≤ Real.log C₁ + X + Pv := by
    have hθi : 0 < θ⁻¹ := inv_pos.2 hθ
    have h1 : Real.log K₁ ≤ Real.log (C₁ * v⁻¹ * θ⁻¹) := Real.log_le_log (by linarith) hK₁le
    rw [Real.log_mul (by positivity) hθi.ne', Real.log_mul (by positivity) hvi.ne'] at h1
    have h2 : Real.log v⁻¹ ≤ X := by
      have := Real.log_le_sub_one_of_pos hvi
      linarith
    linarith
  -- the four terms
  have hT1 : Real.log (4 * max Ccat 1 * max J 1) / D₀ ≤
      (c₁ + |Ap|) / D₀ * X ^ k₄₅ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hD₀]
    have h1 : |Ap| * X ^ k' ≤ |Ap| * X ^ k₄₅ := mul_le_mul_of_nonneg_left hXk' (abs_nonneg _)
    have h2 : c₁ ≤ c₁ * X ^ k₄₅ := le_mul_of_one_le_right hc₁0 hX45
    have h3 : (c₁ + |Ap|) * X ^ k₄₅ = c₁ * X ^ k₄₅ + |Ap| * X ^ k₄₅ := by ring
    rw [h3]
    linarith
  have hT2 : 4 * (2 * Real.log k + Real.log (4 * K₁ * max J 1) + 1) / (κ / 2) ≤
      8 / κ * (c₂ + 1 + 2 * |Ap|) * X ^ k₄₅ := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    have heq : 4 * (2 * Real.log k + (Real.log 4 + Real.log K₁ + Real.log (max J 1)) + 1) / (κ / 2) =
        8 / κ * (2 * Real.log k + (Real.log 4 + Real.log K₁ + Real.log (max J 1)) + 1) := by
      rw [div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm (4 * _) 2, ← mul_assoc]
      norm_num
    rw [heq, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : |Ap| * X ^ k' ≤ |Ap| * X ^ k₄₅ := mul_le_mul_of_nonneg_left hXk' (abs_nonneg _)
    have hX1' : X ≤ X ^ k₄₅ := by
      have := hXk 1 (by linarith)
      rwa [Real.rpow_one] at this
    have h3 : c₂ ≤ c₂ * X ^ k₄₅ := le_mul_of_one_le_right hc₂0 hX45
    have h4 : (c₂ + 1 + 2 * |Ap|) * X ^ k₄₅ = c₂ * X ^ k₄₅ + X ^ k₄₅ + 2 * (|Ap| * X ^ k₄₅) := by ring
    rw [h4]
    have hc₂def : c₂ = 2 * Real.log k + Real.log 4 + Real.log C₁ + 1 := rfl
    linarith
  have hM₀ : max (a⁻¹ * Pv * Pv) 1 ≤ (1 + Ap ^ 2) * X ^ (2 * k' + 1) := by
    have hX2 : 1 ≤ X ^ (2 * k' + 1) := Real.one_le_rpow hX1 (by positivity)
    have hprod : a⁻¹ * Pv * Pv ≤ Ap ^ 2 * X ^ (2 * k' + 1) := by
      have hsplit : X ^ (2 * k' + 1) = X ^ k' * X ^ k' * X := by
        rw [Real.rpow_add hX0, Real.rpow_one, two_mul, Real.rpow_add hX0]
      rw [hsplit]
      have ha' : a⁻¹ ≤ X := by linarith
      have hPv' : Pv * Pv ≤ (|Ap| * X ^ k') * (|Ap| * X ^ k') :=
        mul_le_mul hPvle hPvle hPv0 (by positivity)
      calc a⁻¹ * Pv * Pv = a⁻¹ * (Pv * Pv) := by ring
        _ ≤ X * ((|Ap| * X ^ k') * (|Ap| * X ^ k')) :=
            mul_le_mul ha' hPv' (by positivity) hX0.le
        _ = Ap ^ 2 * (X ^ k' * X ^ k' * X) := by rw [← sq_abs Ap]; ring
    refine max_le ?_ ?_
    · nlinarith [hXpos (2 * k' + 1)]
    · nlinarith [hXpos (2 * k' + 1)]
  have hT3 : 64 * k * D₀ * (max (a⁻¹ * Pv * Pv) 1) ^ 2 / ((κ / 2) ^ 2) ≤
      256 * k * D₀ / κ ^ 2 * (1 + Ap ^ 2) ^ 2 * X ^ k₄₅ := by
    have hM0 : 0 ≤ max (a⁻¹ * Pv * Pv) 1 := le_trans zero_le_one (le_max_right _ _)
    have hsq : (max (a⁻¹ * Pv * Pv) 1) ^ 2 ≤ (1 + Ap ^ 2) ^ 2 * X ^ k₄₅ := by
      have h1 := pow_le_pow_left₀ hM0 hM₀ 2
      have hXX : X ^ (2 * k' + 1) * X ^ (2 * k' + 1) = X ^ k₄₅ := by
        rw [← Real.rpow_add hX0, hk45]
        congr 1
        ring
      have hpow2 : ((1 + Ap ^ 2) * X ^ (2 * k' + 1)) ^ 2 = (1 + Ap ^ 2) ^ 2 * X ^ k₄₅ := by
        rw [mul_pow, sq (X ^ (2 * k' + 1)), hXX]
      rw [hpow2] at h1
      exact h1
    have heq : 64 * k * D₀ * (max (a⁻¹ * Pv * Pv) 1) ^ 2 / ((κ / 2) ^ 2) =
        256 * k * D₀ / κ ^ 2 * (max (a⁻¹ * Pv * Pv) 1) ^ 2 := by
      field_simp
      ring
    rw [heq, mul_assoc (256 * k * D₀ / κ ^ 2)]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hT4 : 2 * Real.log k ≤ 2 * Real.log k * X ^ k₄₅ :=
    le_mul_of_one_le_right (by positivity) hX45
  have hpoly : polyB ((c₁ + |Ap|) / D₀ + 8 / κ * (c₂ + 1 + 2 * |Ap|) +
      256 * k * D₀ / κ ^ 2 * (1 + Ap ^ 2) ^ 2 + 2 * Real.log k) k₄₅ a⁻¹ v⁻¹ =
      ((c₁ + |Ap|) / D₀ + 8 / κ * (c₂ + 1 + 2 * |Ap|) +
      256 * k * D₀ / κ ^ 2 * (1 + Ap ^ 2) ^ 2 + 2 * Real.log k) * X ^ k₄₅ := rfl
  rw [hpoly] at hℓ
  have hXk0 : 0 ≤ X ^ k₄₅ := (hXpos k₄₅).le
  have hc1 : 0 ≤ (c₁ + |Ap|) / D₀ * X ^ k₄₅ :=
    mul_nonneg (div_nonneg (add_nonneg hc₁0 (abs_nonneg _)) hD₀.le) hXk0
  have hc2 : 0 ≤ 8 / κ * (c₂ + 1 + 2 * |Ap|) * X ^ k₄₅ :=
    mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hκ.le)
      (add_nonneg (add_nonneg hc₂0 zero_le_one) (mul_nonneg zero_le_two (abs_nonneg _)))) hXk0
  have hc3 : 0 ≤ 256 * k * D₀ / κ ^ 2 * (1 + Ap ^ 2) ^ 2 * X ^ k₄₅ :=
    mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) hD₀.le)
      (sq_nonneg κ)) (sq_nonneg _)) hXk0
  have hc4 : 0 ≤ 2 * Real.log k * X ^ k₄₅ := mul_nonneg (mul_nonneg zero_le_two hlogk) hXk0
  have hsum : ((c₁ + |Ap|) / D₀ + 8 / κ * (c₂ + 1 + 2 * |Ap|) +
      256 * k * D₀ / κ ^ 2 * (1 + Ap ^ 2) ^ 2 + 2 * Real.log k) * X ^ k₄₅ =
      (c₁ + |Ap|) / D₀ * X ^ k₄₅ + 8 / κ * (c₂ + 1 + 2 * |Ap|) * X ^ k₄₅ +
        256 * k * D₀ / κ ^ 2 * (1 + Ap ^ 2) ^ 2 * X ^ k₄₅ + 2 * Real.log k * X ^ k₄₅ := by ring
  rw [hsum] at hℓ
  refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
  · exact hT1.trans ((((le_add_of_nonneg_right hc2).trans (le_add_of_nonneg_right hc3)).trans
      (le_add_of_nonneg_right hc4)).trans hℓ)
  · exact hT2.trans ((((le_add_of_nonneg_left hc1).trans (le_add_of_nonneg_right hc3)).trans
      (le_add_of_nonneg_right hc4)).trans hℓ)
  · exact hT3.trans (((le_add_of_nonneg_left (add_nonneg hc1 hc2)).trans
      (le_add_of_nonneg_right hc4)).trans hℓ)
  · exact hT4.trans ((le_add_of_nonneg_left (add_nonneg (add_nonneg hc1 hc2) hc3)).trans hℓ)

end HigherDimLQGContinuity
