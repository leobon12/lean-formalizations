import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Numerics of Lemma 3.4 (packet P8a)

Packet P8a, blueprint Part A, Lemma `a:lem34` (proof, "Constants" and "Contradiction"; NA1 item 26, R10; erratum
EA19): the elementary real inequalities behind the quantified contradiction with `A = 3`, `δ = v/100`, `e = v⁴/100`,
`n(v) = C₅ (1/v)^{M₃+1}` and `τ ≤ c₄ v^{M₃+2}`.

* `p8a_half_le_log_one_add`: `v/2 ≤ log(1 + v)` for `0 ≤ v ≤ 1`.
* `p8a_cantelli_rate`: with `t = log(1 + v)`, `c₁ v² ≤ t²/(σ² + t²)`, `c₁ = 1/(4(σ² + 1))`.
* `p8a_contra`: the contradiction (3.11): `D₀ ≥ v³`, `E₀ ≤ (1 + v) D₀` and
  `D₀ ≤ ((1 + 2v)⁻¹ + v/100) E₀ + v⁴/100` are incompatible for `0 < v < 1`.
* `p8a_numerics`: a depth constant `C₅` such that `n(v) = C₅ (1/v)^{M₃+1}` satisfies Proposition 3.3's depth
  condition at `R = 1`, `δ = v/100`, `e = v⁴/100` and makes its failure bound `≤ c₁ v²/4`, for `0 < v ≤ 1`.
* `p8a_drift`: `τ ≤ (c₃/(100 C₅)) v^{M₃+2}` gives Proposition 3.3's drift condition `τ n(v) ≤ c₃ v/100`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-! ## Elementary bounds -/

/-- `v/2 ≤ log(1 + v)` for `0 ≤ v ≤ 1`. -/
theorem p8a_half_le_log_one_add {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) : v / 2 ≤ Real.log (1 + v) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have habs : |v / 2| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have h := Real.abs_exp_sub_one_sub_id_le habs
  have h' := (abs_le.1 h).2
  nlinarith

/-- `log(1 + v) ≤ v` for `v > -1`. -/
theorem p8a_log_one_add_le {v : ℝ} (hv : -1 < v) : Real.log (1 + v) ≤ v := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + v by linarith)
  linarith

/-- **Cantelli's rate** at `t = log(1 + v)`: `c₁ v² ≤ t²/(σ² + t²)` with `c₁ = 1/(4(σ² + 1))`, for `0 < v ≤ 1`. -/
theorem p8a_cantelli_rate {σ2 v : ℝ} (hσ2 : 0 ≤ σ2) (hv : 0 < v) (hv1 : v ≤ 1) :
    1 / (4 * (σ2 + 1)) * v ^ 2 ≤ Real.log (1 + v) ^ 2 / (σ2 + Real.log (1 + v) ^ 2) := by
  set t := Real.log (1 + v) with ht
  have ht1 : v / 2 ≤ t := p8a_half_le_log_one_add hv.le hv1
  have ht2 : t ≤ v := p8a_log_one_add_le (by linarith)
  have ht0 : 0 < t := by linarith
  have ht3 : t ^ 2 ≤ 1 := by nlinarith
  have hsq : v ^ 2 / 4 ≤ t ^ 2 := by nlinarith
  have hpos : 0 < σ2 + t ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have : 1 / (4 * (σ2 + 1)) * v ^ 2 * (σ2 + t ^ 2) ≤ 1 / (4 * (σ2 + 1)) * v ^ 2 * (σ2 + 1) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc 1 / (4 * (σ2 + 1)) * v ^ 2 * (σ2 + t ^ 2) ≤ 1 / (4 * (σ2 + 1)) * v ^ 2 * (σ2 + 1) := this
    _ = v ^ 2 / 4 := by field_simp
    _ ≤ t ^ 2 := hsq

/-- **The contradiction (3.11)** of Lemma 3.4 (NA1 R10): for `0 < v < 1`, the three conditions `D₀ ≥ v³`,
`E₀ ≤ (1 + v) D₀` and `D₀ ≤ ((1 + 2v)⁻¹ + v/100) E₀ + v⁴/100` are incompatible, since
`((1 + 2v)⁻¹ + v/100)(1 + v) + v/100 = 1 - v/(1 + 2v) + v(2 + v)/100 < 1`. -/
theorem p8a_contra {v D₀ E₀ : ℝ} (hv : 0 < v) (hv1 : v < 1) (hD₀ : v ^ 3 ≤ D₀)
    (hE : E₀ ≤ (1 + v) * D₀) (hcomp : D₀ ≤ ((1 + 2 * v)⁻¹ + v / 100) * E₀ + v ^ 4 / 100) : False := by
  have hD₀pos : 0 < D₀ := lt_of_lt_of_le (by positivity) hD₀
  have h12 : 0 < 1 + 2 * v := by linarith
  set a : ℝ := (1 + 2 * v)⁻¹ with ha
  have ha0 : 0 < a := inv_pos.2 h12
  have ha1 : a * (1 + 2 * v) = 1 := inv_mul_cancel₀ h12.ne'
  have hc0 : 0 ≤ a + v / 100 := by positivity
  have hE' : (a + v / 100) * E₀ ≤ (a + v / 100) * ((1 + v) * D₀) := mul_le_mul_of_nonneg_left hE hc0
  have h4 : v ^ 4 / 100 ≤ v / 100 * D₀ := by
    have : v ^ 4 = v * v ^ 3 := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hD₀ hv.le
    linarith
  -- the bracket is `< 1`
  have hkey : (a + v / 100) * (1 + v) + v / 100 < 1 := by
    have ha3 : 1 / 3 < a := by
      rw [ha, one_div, inv_lt_inv₀ (by norm_num) h12]
      linarith
    nlinarith
  have : D₀ ≤ ((a + v / 100) * (1 + v) + v / 100) * D₀ := by nlinarith
  nlinarith

/-! ## Powers of `1/v` -/

/-- `(v/100)^{-M} = 100^M (1/v)^M` for `v > 0`. -/
theorem p8a_rpow_neg_div {v : ℝ} (hv : 0 < v) (M : ℝ) :
    (v / 100) ^ (-M) = (100 : ℝ) ^ M * v⁻¹ ^ M := by
  rw [Real.rpow_neg (by positivity), Real.div_rpow hv.le (by norm_num), Real.inv_rpow hv.le, inv_div,
    div_eq_mul_inv]

/-- `(v/100)^M (1/v)^{M+1} = (1/v)/100^M` for `v > 0`. -/
theorem p8a_rpow_div_mul {v : ℝ} (hv : 0 < v) (M : ℝ) :
    (v / 100) ^ M * v⁻¹ ^ (M + 1) = v⁻¹ / (100 : ℝ) ^ M := by
  have h100 : (0 : ℝ) < (100 : ℝ) ^ M := Real.rpow_pos_of_pos (by norm_num) M
  have hvM : (0 : ℝ) < v ^ M := Real.rpow_pos_of_pos hv M
  rw [Real.div_rpow hv.le (by norm_num), Real.rpow_add (inv_pos.2 hv), Real.rpow_one, Real.inv_rpow hv.le]
  field_simp

/-- `w^x ≤ e^{x w}` for `w > 0`, `x ≥ 0`. -/
theorem p8a_rpow_le_exp {w x : ℝ} (hw : 0 < w) (hx : 0 ≤ x) : w ^ x ≤ Real.exp (x * w) := by
  rw [Real.rpow_def_of_pos hw]
  apply Real.exp_le_exp.2
  have := Real.log_le_sub_one_of_pos hw
  nlinarith

/-- The logarithmic bracket of Proposition 3.3 at `R = 1`, `δ = v/100`, `e = v⁴/100`:
`1 + log 2 + log(100/v⁴) + log(100/v) ≤ (1 + log 2 + 2 log 100 + 5)/v` for `0 < v ≤ 1`. -/
theorem p8a_log_bracket_le {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    1 + Real.log (1 + 1) + Real.log (v ^ 4 / 100)⁻¹ + Real.log (v / 100)⁻¹ ≤
      (1 + Real.log 2 + 2 * Real.log 100 + 5) * v⁻¹ := by
  have h1 : Real.log (v ^ 4 / 100)⁻¹ = Real.log 100 + 4 * Real.log v⁻¹ := by
    rw [inv_div, Real.log_div (by norm_num) (by positivity), Real.log_pow, Real.log_inv]
    push_cast
    ring
  have h2 : Real.log (v / 100)⁻¹ = Real.log 100 + Real.log v⁻¹ := by
    rw [inv_div, Real.log_div (by norm_num) hv.ne', Real.log_inv]
    ring
  have hw1 : 1 ≤ v⁻¹ := one_le_inv_iff₀.2 ⟨hv, hv1⟩
  have hlogw : Real.log v⁻¹ ≤ v⁻¹ := by
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hv)
    linarith
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog100 : 0 ≤ Real.log 100 := Real.log_nonneg (by norm_num)
  rw [h1, h2, show (1 : ℝ) + 1 = 2 by norm_num]
  have hA : 0 ≤ 1 + Real.log 2 + 2 * Real.log 100 := by linarith
  have : (1 + Real.log 2 + 2 * Real.log 100) * 1 ≤ (1 + Real.log 2 + 2 * Real.log 100) * v⁻¹ :=
    mul_le_mul_of_nonneg_left hw1 hA
  nlinarith

/-! ## The depth `n(v)` -/

/-- **The depth of Lemma 3.4** (blueprint `a:lem34`, "Constants"; EA19): for Proposition 3.3's constants
`M₃, C₃, c₃ > 0` and `c₁ > 0` there is `C₅ > 0` such that for `0 < v ≤ 1` the depth `n(v) = C₅ (1/v)^{M₃+1}`
satisfies Proposition 3.3's depth condition at `R = 1`, `δ = v/100`, `e = v⁴/100`, and its failure bound is at most
`c₁ v²/4`. -/
theorem p8a_numerics {M₃ C₃ c₃ c₁ : ℝ} (hM₃ : 0 < M₃) (hC₃ : 0 < C₃) (hc₃ : 0 < c₃) (hc₁ : 0 < c₁) :
    ∃ C₅ : ℝ, 0 < C₅ ∧ ∀ v : ℝ, 0 < v → v ≤ 1 →
      C₃ * (v / 100) ^ (-M₃) *
          (1 + Real.log (1 + 1) + Real.log (v ^ 4 / 100)⁻¹ + Real.log (v / 100)⁻¹) ≤
        C₅ * v⁻¹ ^ (M₃ + 1) ∧
      C₃ * (1 : ℝ) ^ M₃ * (v / 100) ^ (-M₃) *
          Real.exp (-c₃ * (v / 100) ^ M₃ * (C₅ * v⁻¹ ^ (M₃ + 1))) ≤ c₁ * v ^ 2 / 4 := by
  set A₁ : ℝ := 1 + Real.log 2 + 2 * Real.log 100 + 5 with hA₁
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog100 : 0 ≤ Real.log 100 := Real.log_nonneg (by norm_num)
  have hA₁ : 0 < A₁ := by rw [hA₁]; linarith
  set P : ℝ := (100 : ℝ) ^ M₃ with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos (by norm_num) M₃
  set B : ℝ := 4 * C₃ * P / c₁ with hB
  have hB0 : 0 < B := by positivity
  set L : ℝ := max 0 (Real.log B) with hL
  have hL0 : 0 ≤ L := le_max_left _ _
  have hLB : Real.log B ≤ L := le_max_right _ _
  set C₅ : ℝ := C₃ * P * A₁ + (M₃ + 2 + L) * P / c₃ with hC₅
  have hC₅a : C₃ * P * A₁ ≤ C₅ := by
    have : 0 ≤ (M₃ + 2 + L) * P / c₃ := by positivity
    linarith
  have hC₅b : (M₃ + 2 + L) * P / c₃ ≤ C₅ := by
    have : 0 ≤ C₃ * P * A₁ := by positivity
    linarith
  have hC₅0 : 0 < C₅ := lt_of_lt_of_le (by positivity) hC₅a
  refine ⟨C₅, hC₅0, fun v hv hv1 => ⟨?_, ?_⟩⟩
  · -- the depth condition
    have hbr := p8a_log_bracket_le hv hv1
    rw [p8a_rpow_neg_div hv M₃, Real.rpow_add (inv_pos.2 hv), Real.rpow_one]
    have hwM : 0 ≤ v⁻¹ ^ M₃ := Real.rpow_nonneg (inv_pos.2 hv).le M₃
    calc C₃ * (P * v⁻¹ ^ M₃) * (1 + Real.log (1 + 1) + Real.log (v ^ 4 / 100)⁻¹ + Real.log (v / 100)⁻¹)
        ≤ C₃ * (P * v⁻¹ ^ M₃) * (A₁ * v⁻¹) := mul_le_mul_of_nonneg_left hbr (by positivity)
      _ = C₃ * P * A₁ * (v⁻¹ ^ M₃ * v⁻¹) := by ring
      _ ≤ C₅ * (v⁻¹ ^ M₃ * v⁻¹) := mul_le_mul_of_nonneg_right hC₅a (by positivity)
  · -- the failure bound
    set w : ℝ := v⁻¹ with hw
    have hw0 : 0 < w := inv_pos.2 hv
    have hw1 : 1 ≤ w := one_le_inv_iff₀.2 ⟨hv, hv1⟩
    have hexp : -c₃ * (v / 100) ^ M₃ * (C₅ * w ^ (M₃ + 1)) = -(c₃ * C₅ / P) * w := by
      have h := p8a_rpow_div_mul hv M₃
      rw [← hw] at h
      calc -c₃ * (v / 100) ^ M₃ * (C₅ * w ^ (M₃ + 1)) = -c₃ * C₅ * ((v / 100) ^ M₃ * w ^ (M₃ + 1)) := by ring
        _ = -c₃ * C₅ * (w / P) := by rw [h]
        _ = -(c₃ * C₅ / P) * w := by ring
    have hκ : M₃ + 2 + L ≤ c₃ * C₅ / P := by
      rw [le_div_iff₀ hP0]
      have := mul_le_mul_of_nonneg_left hC₅b hc₃.le
      have heq : c₃ * ((M₃ + 2 + L) * P / c₃) = (M₃ + 2 + L) * P := by field_simp
      linarith
    rw [hexp, Real.one_rpow, mul_one, p8a_rpow_neg_div hv M₃]
    -- `w^{M₃} w² ≤ e^{(M₃+2) w}`
    have hpow : w ^ M₃ * w ^ 2 ≤ Real.exp ((M₃ + 2) * w) := by
      have h := p8a_rpow_le_exp hw0 (show 0 ≤ M₃ + 2 by linarith)
      rw [Real.rpow_add hw0, Real.rpow_two] at h
      exact h
    have hv2 : v ^ 2 = (w ^ 2)⁻¹ := by rw [hw, inv_pow, inv_inv]
    rw [hv2]
    have hw2 : 0 < w ^ 2 := by positivity
    rw [show c₁ * (w ^ 2)⁻¹ / 4 = c₁ / 4 / w ^ 2 by field_simp, le_div_iff₀ hw2]
    -- reduce to `C₃ P e^{(M₃ + 2 - κ) w} ≤ c₁/4`
    have hstep : C₃ * (P * w ^ M₃) * Real.exp (-(c₃ * C₅ / P) * w) * w ^ 2 ≤
        C₃ * P * Real.exp (-L) := by
      have h1 : C₃ * (P * w ^ M₃) * Real.exp (-(c₃ * C₅ / P) * w) * w ^ 2 =
          C₃ * P * ((w ^ M₃ * w ^ 2) * Real.exp (-(c₃ * C₅ / P) * w)) := by ring
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (w ^ M₃ * w ^ 2) * Real.exp (-(c₃ * C₅ / P) * w)
          ≤ Real.exp ((M₃ + 2) * w) * Real.exp (-(c₃ * C₅ / P) * w) :=
            mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
        _ = Real.exp ((M₃ + 2 - c₃ * C₅ / P) * w) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (-L) := by
            apply Real.exp_le_exp.2
            have h2 : (M₃ + 2 - c₃ * C₅ / P) * w ≤ (-L) * w :=
              mul_le_mul_of_nonneg_right (by linarith) hw0.le
            have h3 : (-L) * w ≤ -L := by nlinarith
            linarith
    have hexpL : C₃ * P * Real.exp (-L) ≤ c₁ / 4 := by
      have h1 : Real.exp (-L) ≤ Real.exp (-Real.log B) := Real.exp_le_exp.2 (by linarith)
      rw [Real.exp_neg (Real.log B), Real.exp_log hB0] at h1
      calc C₃ * P * Real.exp (-L) ≤ C₃ * P * B⁻¹ := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = c₁ / 4 := by rw [hB]; field_simp
    linarith

/-- **The drift condition** of Lemma 3.4: with `c₄ = c₃/(100 C₅)`, `τ ≤ c₄ v^{M₃+2}` gives
`τ · C₅ (1/v)^{M₃+1} ≤ c₃ (v/100)`. -/
theorem p8a_drift {M₃ C₅ c₃ v τ : ℝ} (hC₅ : 0 < C₅) (hv : 0 < v)
    (hτv : τ ≤ c₃ / (100 * C₅) * v ^ (M₃ + 2)) :
    τ * (C₅ * v⁻¹ ^ (M₃ + 1)) ≤ c₃ * (v / 100) := by
  have hw : 0 ≤ C₅ * v⁻¹ ^ (M₃ + 1) := by positivity
  have hprod : v ^ (M₃ + 2) * v⁻¹ ^ (M₃ + 1) = v := by
    rw [show M₃ + 2 = (M₃ + 1) + 1 by ring, Real.rpow_add hv, Real.rpow_one, Real.inv_rpow hv.le]
    have : (0 : ℝ) < v ^ (M₃ + 1) := Real.rpow_pos_of_pos hv _
    field_simp
  calc τ * (C₅ * v⁻¹ ^ (M₃ + 1)) ≤ c₃ / (100 * C₅) * v ^ (M₃ + 2) * (C₅ * v⁻¹ ^ (M₃ + 1)) :=
        mul_le_mul_of_nonneg_right hτv hw
    _ = c₃ / 100 * (v ^ (M₃ + 2) * v⁻¹ ^ (M₃ + 1)) := by field_simp
    _ = c₃ * (v / 100) := by rw [hprod]; ring

end HigherDimLQGContinuity
