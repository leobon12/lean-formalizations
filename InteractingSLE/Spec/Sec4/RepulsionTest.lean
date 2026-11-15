/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The test function of the localized repulsion criterion (Aux. lemma 5)

Packet PROVE-SEC4-A2. Specification §2.2, proof of Aux. lemma 5 (`source/spec/p001-048.md`, (RP2)):
for `0 < y ≤ a` put `F(y) = ∫_y^a e^{2Cs/κ}/s ds`. Then `F ≥ 0`, `F(a) = 0`, `F(y) ↑ ∞` as `y ↓ 0`,
`F'(y) = −e^{2Cy/κ}/y` and `κ/2 F'' + (κ/(2y) − C) F' = 0`.

Itô's formula in expectation (`LocalTime.integral_sub_eq_of_isTanakaPath`) needs a `C²` function on
all of `ℝ`. For `ε > 0` we therefore extend `F` from `[ε, ∞)`: `repulsionF2 η ε` is the continuous
function `y ↦ F''(max y ε)`, `repulsionF1 η ε` its primitive normalized by `F'(ε)`, and
`repulsionF η ε a` the primitive of that, vanishing at `a` (here `η = 2C/κ`). On `[ε, ∞)` these are
`F'' , F'` (`repulsionF1_eq`, `repulsionF2_eq`), and on `[ε, a]` the function is
`F = repulsionInt η a` (`repulsionF_eq`).

Main statements:
* `hasDerivAt_repulsionF`, `hasDerivAt_repulsionF1`, `continuous_repulsionF2`: the `C²` regularity;
* `repulsionDeriv_generator`: the identity (RP2), `κ/2 F'' + (κ/(2y) − C) F' = 0` for `η = 2C/κ`;
* `log_sub_log_le_repulsionInt`, `repulsionInt_antitoneOn`, `repulsionInt_nonneg`: the bounds on
  `F` used in the hitting estimate (RP3).
-/

noncomputable section

open Real Set MeasureTheory intervalIntegral

namespace InteractingSLE.Sec4.Repulsion

/-- The derivative `F'(y) = −e^{ηy}/y` of the source's test function (with `η = 2C/κ`). -/
def repulsionDeriv (η y : ℝ) : ℝ := -(exp (η * y) / y)

/-- The second derivative `F''(y) = e^{ηy} (y⁻² − η/y)`. -/
def repulsionDeriv2 (η y : ℝ) : ℝ := exp (η * y) * ((y ^ 2)⁻¹ - η / y)

/-- The continuous extension `y ↦ F''(max y ε)` of `F''` from `[ε, ∞)` to `ℝ`. -/
def repulsionF2 (η ε y : ℝ) : ℝ := repulsionDeriv2 η (max y ε)

/-- The primitive of `repulsionF2` with value `F'(ε)` at `ε`. -/
def repulsionF1 (η ε y : ℝ) : ℝ := repulsionDeriv η ε + ∫ r in ε..y, repulsionF2 η ε r

/-- The primitive of `repulsionF1` vanishing at `a`: a `C²` function on `ℝ` equal to `F` on `[ε, a]`. -/
def repulsionF (η ε a y : ℝ) : ℝ := ∫ r in a..y, repulsionF1 η ε r

/-- The source's test function `F(y) = ∫_y^a e^{ηs}/s ds`. -/
def repulsionInt (η a y : ℝ) : ℝ := ∫ r in y..a, exp (η * r) / r

lemma hasDerivAt_repulsionDeriv (η : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (repulsionDeriv η) (repulsionDeriv2 η y) y := by
  have h1 : HasDerivAt (fun y => exp (η * y)) (exp (η * y) * η) y := by
    simpa using ((hasDerivAt_id y).const_mul η).exp
  have h2 := (h1.div (hasDerivAt_id' y) hy.ne').neg
  refine h2.congr_deriv ?_
  unfold repulsionDeriv2
  field_simp
  ring

lemma continuousOn_repulsionDeriv2 (η : ℝ) : ContinuousOn (repulsionDeriv2 η) (Ioi 0) := by
  intro y hy
  have hy0 : y ≠ 0 := (mem_Ioi.1 hy).ne'
  unfold repulsionDeriv2
  refine ContinuousAt.continuousWithinAt ?_
  refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt).mul
    ((((continuous_pow 2).continuousAt).inv₀ (pow_ne_zero 2 hy0)).sub
      (continuousAt_const.div continuousAt_id hy0))

lemma continuous_repulsionF2 (η : ℝ) {ε : ℝ} (hε : 0 < ε) : Continuous (repulsionF2 η ε) := by
  unfold repulsionF2
  refine (continuousOn_repulsionDeriv2 η).comp_continuous (continuous_id.max continuous_const)
    fun y => ?_
  exact mem_Ioi.2 (lt_of_lt_of_le hε (le_max_right _ _))

lemma hasDerivAt_repulsionF1 (η : ℝ) {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    HasDerivAt (repulsionF1 η ε) (repulsionF2 η ε y) y := by
  have := ((continuous_repulsionF2 η hε).integral_hasStrictDerivAt ε y).hasDerivAt
  exact this.const_add _

lemma continuous_repulsionF1 (η : ℝ) {ε : ℝ} (hε : 0 < ε) : Continuous (repulsionF1 η ε) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_repulsionF1 η hε y).continuousAt

lemma hasDerivAt_repulsionF (η : ℝ) {ε : ℝ} (hε : 0 < ε) (a y : ℝ) :
    HasDerivAt (repulsionF η ε a) (repulsionF1 η ε y) y :=
  ((continuous_repulsionF1 η hε).integral_hasStrictDerivAt a y).hasDerivAt

lemma continuous_repulsionF (η : ℝ) {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Continuous (repulsionF η ε a) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_repulsionF η hε a y).continuousAt

lemma repulsionF2_eq (η : ℝ) {ε y : ℝ} (hy : ε ≤ y) : repulsionF2 η ε y = repulsionDeriv2 η y := by
  unfold repulsionF2; rw [max_eq_left hy]

lemma repulsionF1_eq (η : ℝ) {ε y : ℝ} (hε : 0 < ε) (hy : ε ≤ y) :
    repulsionF1 η ε y = repulsionDeriv η y := by
  unfold repulsionF1
  have hFTC : ∫ r in ε..y, repulsionF2 η ε r = repulsionDeriv η y - repulsionDeriv η ε := by
    refine integral_eq_sub_of_hasDerivAt (fun r hr => ?_)
      ((continuous_repulsionF2 η hε).intervalIntegrable _ _)
    rw [uIcc_of_le hy] at hr
    rw [repulsionF2_eq η hr.1]
    exact hasDerivAt_repulsionDeriv η (lt_of_lt_of_le hε hr.1)
  rw [hFTC]; ring

/-- On `[ε, a]` the extension is the source's `F`. -/
lemma repulsionF_eq (η : ℝ) {ε a y : ℝ} (hε : 0 < ε) (hy : ε ≤ y) (hya : y ≤ a) :
    repulsionF η ε a y = repulsionInt η a y := by
  unfold repulsionF repulsionInt
  rw [integral_symm, ← intervalIntegral.integral_neg]
  refine integral_congr fun r hr => ?_
  rw [uIcc_of_le hya] at hr
  simp only [repulsionF1_eq η hε (hy.trans hr.1), repulsionDeriv, neg_neg]

/-- **(RP2)**: `κ/2 F''(y) + (κ/(2y) − C) F'(y) = 0` for `η = 2C/κ`. -/
lemma repulsionDeriv_generator {κ C y : ℝ} (hκ : 0 < κ) (hy : 0 < y) :
    κ / 2 * repulsionDeriv2 (2 * C / κ) y + (κ / (2 * y) - C) * repulsionDeriv (2 * C / κ) y =
      0 := by
  unfold repulsionDeriv repulsionDeriv2
  field_simp
  ring

lemma repulsionDeriv_neg (η : ℝ) {y : ℝ} (hy : 0 < y) : repulsionDeriv η y < 0 := by
  unfold repulsionDeriv
  exact neg_lt_zero.2 (div_pos (exp_pos _) hy)

lemma intervalIntegrable_exp_div {η y a : ℝ} (hy : 0 < y) (hya : y ≤ a) :
    IntervalIntegrable (fun r => exp (η * r) / r) volume y a := by
  refine ContinuousOn.intervalIntegrable fun r hr => ?_
  rw [uIcc_of_le hya] at hr
  exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousAt.div continuousAt_id
    (lt_of_lt_of_le hy hr.1).ne').continuousWithinAt

/-- `F(y) ≥ log a − log y` for `0 < y ≤ a` and `η ≥ 0`. -/
lemma log_sub_log_le_repulsionInt {η a y : ℝ} (hη : 0 ≤ η) (hy : 0 < y) (hya : y ≤ a) :
    log a - log y ≤ repulsionInt η a y := by
  have ha : 0 < a := lt_of_lt_of_le hy hya
  have hlog : ∫ r in y..a, r⁻¹ = log a - log y := by
    rw [integral_inv_of_pos hy ha, log_div ha.ne' hy.ne']
  rw [← hlog]
  refine integral_mono_on hya (intervalIntegrable_inv (fun r hr => ?_) continuousOn_id)
    (intervalIntegrable_exp_div hy hya) fun r hr => ?_
  · rw [uIcc_of_le hya] at hr; exact (lt_of_lt_of_le hy hr.1).ne'
  · have hr0 : 0 < r := lt_of_lt_of_le hy hr.1
    rw [div_eq_mul_inv]
    refine le_mul_of_one_le_left (inv_nonneg.2 hr0.le) ?_
    exact one_le_exp (mul_nonneg hη hr0.le)

lemma repulsionInt_nonneg {η a y : ℝ} (hy : 0 < y) (hya : y ≤ a) : 0 ≤ repulsionInt η a y :=
  integral_nonneg hya fun _ hr => div_nonneg (exp_pos _).le (hy.trans_le hr.1).le

/-- `F` is nonincreasing on `(0, a]`. -/
lemma repulsionInt_le {η a y y' : ℝ} (hy : 0 < y) (hyy : y ≤ y') (hya : y' ≤ a) :
    repulsionInt η a y' ≤ repulsionInt η a y := by
  unfold repulsionInt
  rw [← integral_add_adjacent_intervals (b := y') (intervalIntegrable_exp_div hy hyy)
    (intervalIntegrable_exp_div (hy.trans_le hyy) hya)]
  refine le_add_of_nonneg_left (integral_nonneg hyy fun r hr => ?_)
  exact div_nonneg (exp_pos _).le (hy.trans_le hr.1).le

/-- `F(ε) → ∞` as `ε ↓ 0`: for every bound `K` there is `ε₀ > 0` with `K ≤ F(ε)` on `(0, ε₀]`. -/
lemma exists_le_repulsionInt {η a : ℝ} (hη : 0 ≤ η) (ha : 0 < a) (K : ℝ) :
    ∃ ε₀, 0 < ε₀ ∧ ε₀ ≤ a ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → K ≤ repulsionInt η a ε := by
  refine ⟨min a (exp (log a - K)), lt_min ha (exp_pos _), min_le_left _ _, fun ε hε hεle => ?_⟩
  have hεa : ε ≤ a := hεle.trans (min_le_left _ _)
  refine le_trans ?_ (log_sub_log_le_repulsionInt hη hε hεa)
  have : log ε ≤ log a - K := by
    rw [← log_exp (log a - K)]
    exact log_le_log hε (hεle.trans (min_le_right _ _))
  linarith

end InteractingSLE.Sec4.Repulsion
