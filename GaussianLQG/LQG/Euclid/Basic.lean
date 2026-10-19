import GaussianLQG.Probability.Gaussian
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Elementary tools for the Euclidean approximation (blueprint Lemma `lem:euclidean`)

* `abs_exp_sub_one_le_mul`: `|e^x - 1| ≤ |x| (1 + e^x)` (blueprint Lemma `lem:euclidean`, Step 1).
* Deterministic bounds on `(0, 2ρ]`: `√r · √v ≤ √(1 + 2ρc)` when `v ≤ log⁺(1/r) + c`
  (`sqrt_mul_sqrt_le_of_le_posLog`, from `r log⁺(1/r) ≤ 1`), and `√r |log r| ≤ 2 + 4ρ²`
  (`sqrt_mul_abs_log_le`).
* `L^p` tools: the formula `eLpNorm_ofReal_eq`, the `L^p` norm of a centered Gaussian
  (`eLpNorm_of_hasLaw_gaussianReal`: `‖Z‖_p = √v ‖N‖_p`), the Hölder triple `(2p, 2p, p)`
  (`holderTriple_two_mul`), constants (`eLpNorm_const_prob`), and domination by a multiple of a
  `[0, ∞]`-valued variable with bounded moment (`eLpNorm_le_of_enorm_le_mul`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

/-! ## Real inequalities -/

/-- `|e^x - 1| ≤ |x| (1 + e^x)` for every real `x`. -/
theorem abs_exp_sub_one_le_mul (x : ℝ) : |Real.exp x - 1| ≤ |x| * (1 + Real.exp x) := by
  have hex := Real.exp_pos x
  rcases le_or_gt 0 x with hx | hx
  · have h1 : 1 - x ≤ Real.exp (-x) := by
      have := Real.add_one_le_exp (-x)
      linarith
    have h2 : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h3 : 0 ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h4 : Real.exp x * (1 - x) ≤ 1 := by
      calc Real.exp x * (1 - x) ≤ Real.exp x * Real.exp (-x) :=
            mul_le_mul_of_nonneg_left h1 hex.le
        _ = 1 := h2
    rw [abs_of_nonneg h3, abs_of_nonneg hx]
    nlinarith
  · have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have h3 : Real.exp x - 1 < 0 := by
      have := Real.exp_lt_one_iff.2 hx
      linarith
    have h4 : 0 ≤ -x * Real.exp x := mul_nonneg (by linarith) hex.le
    rw [abs_of_neg h3, abs_of_neg hx]
    nlinarith

/-- `r log⁺(1/r) ≤ 1` for `r > 0`. -/
theorem mul_posLog_inv_le_one {r : ℝ} (hr : 0 < r) : r * Real.posLog r⁻¹ ≤ 1 := by
  rcases le_or_gt r 1 with h1 | h1
  · have hinv : 1 ≤ |r⁻¹| := by
      rw [abs_of_pos (inv_pos.2 hr)]
      exact one_le_inv_iff₀.2 ⟨hr, h1⟩
    rw [Real.posLog_eq_log hinv, Real.log_inv]
    have h := Real.abs_log_mul_self_lt r hr h1
    have h' : r * -Real.log r ≤ |Real.log r * r| := by
      rw [show r * -Real.log r = -(Real.log r * r) by ring]
      exact neg_le_abs _
    linarith
  · have hinv : |r⁻¹| ≤ 1 := by
      rw [abs_of_pos (inv_pos.2 hr)]
      exact inv_le_one_of_one_le₀ h1.le
    rw [(Real.posLog_eq_zero_iff _).2 hinv, mul_zero]
    exact zero_le_one

/-- If `0 < r ≤ 2ρ` and `0 ≤ v ≤ log⁺(1/r) + c` with `c ≥ 0`, then `√r √v ≤ √(1 + 2ρc)`. -/
theorem sqrt_mul_sqrt_le_of_le_posLog {r v ρ c : ℝ} (hr : 0 < r) (hrρ : r ≤ 2 * ρ) (hc : 0 ≤ c)
    (hv : v ≤ Real.posLog r⁻¹ + c) :
    Real.sqrt r * Real.sqrt v ≤ Real.sqrt (1 + 2 * ρ * c) := by
  rw [← Real.sqrt_mul hr.le]
  apply Real.sqrt_le_sqrt
  have h1 := mul_posLog_inv_le_one hr
  have h2 : r * c ≤ 2 * ρ * c := mul_le_mul_of_nonneg_right hrρ hc
  calc r * v ≤ r * (Real.posLog r⁻¹ + c) := mul_le_mul_of_nonneg_left hv hr.le
    _ = r * Real.posLog r⁻¹ + r * c := by ring
    _ ≤ 1 + 2 * ρ * c := by linarith

/-- `√r |log r| ≤ 2 + 4ρ²` for `0 < r ≤ 2ρ`. -/
theorem sqrt_mul_abs_log_le {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ 2 * ρ) :
    Real.sqrt r * |Real.log r| ≤ 2 + 4 * ρ ^ 2 := by
  rcases le_or_gt r 1 with h1 | h1
  · have h := Real.abs_log_mul_self_rpow_lt r (1 / 2) hr h1 (by norm_num)
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr _), ← Real.sqrt_eq_rpow] at h
    have : (0 : ℝ) ≤ 4 * ρ ^ 2 := by positivity
    rw [mul_comm]
    linarith [show (1 : ℝ) / (1 / 2) = 2 by norm_num]
  · have hlog : |Real.log r| ≤ r := by
      rw [abs_of_nonneg (Real.log_nonneg h1.le)]
      linarith [Real.log_le_sub_one_of_pos hr]
    have hsq : Real.sqrt r ≤ r := by
      rw [Real.sqrt_le_left hr.le]
      nlinarith
    have hr2 : r * r ≤ 4 * ρ ^ 2 := by nlinarith
    calc Real.sqrt r * |Real.log r| ≤ r * r := mul_le_mul hsq hlog (abs_nonneg _) hr.le
      _ ≤ 2 + 4 * ρ ^ 2 := by linarith

/-! ## `L^p` tools -/

section Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- `‖f‖_p = (∫⁻ ‖f‖ₑ^p)^{1/p}` for `p > 0`. -/
theorem eLpNorm_ofReal_eq {ε : Type*} [ENorm ε] {p : ℝ} (hp : 0 < p) (f : α → ε) :
    eLpNorm f (ENNReal.ofReal p) μ = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp).ne' ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le]

/-- `∫⁻ ‖f‖ₑ^p = ‖f‖_p^p` for `p > 0`. -/
theorem lintegral_enorm_rpow_eq {ε : Type*} [ENorm ε] {p : ℝ} (hp : 0 < p) (f : α → ε) :
    ∫⁻ x, ‖f x‖ₑ ^ p ∂μ = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_ofReal_eq hp, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

/-- The `L^p` norm of a constant on a probability space. -/
theorem eLpNorm_const_prob [IsProbabilityMeasure μ] {ε : Type*} [TopologicalSpace ε]
    [ContinuousENorm ε] (c : ε) {p : ℝ≥0∞} (hp : p ≠ 0) :
    eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ := by
  rw [eLpNorm_const c hp (IsProbabilityMeasure.ne_zero μ), measure_univ, ENNReal.one_rpow,
    mul_one]

/-- `(2p, 2p, p)` is a Hölder triple. -/
theorem holderTriple_two_mul {p : ℝ} (hp : 0 < p) :
    ENNReal.HolderTriple (ENNReal.ofReal (2 * p)) (ENNReal.ofReal (2 * p)) (ENNReal.ofReal p) := by
  constructor
  rw [← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_inv_of_pos hp,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  field_simp
  ring

/-- If `‖f‖ₑ ≤ c A` pointwise, `c < ∞`, and `∫⁻ A^p ≤ C`, then `‖f‖_p ≤ c C^{1/p}` (`p > 0`). -/
theorem eLpNorm_le_of_enorm_le_mul {ε : Type*} [ENorm ε] {f : α → ε} {A : α → ℝ≥0∞}
    {c C : ℝ≥0∞} {p : ℝ} (hp : 0 < p) (hc : c ≠ ⊤) (hf : ∀ x, ‖f x‖ₑ ≤ c * A x)
    (hA : ∫⁻ x, A x ^ p ∂μ ≤ C) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ c * C ^ (1 / p) := by
  rw [eLpNorm_ofReal_eq hp]
  have hcp : c ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp.le hc
  calc (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1 / p)
      ≤ (∫⁻ x, (c * A x) ^ p ∂μ) ^ (1 / p) := by
        gcongr with x
        exact hf x
    _ = (c ^ p * ∫⁻ x, A x ^ p ∂μ) ^ (1 / p) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
        rw [lintegral_const_mul' _ _ hcp]
    _ ≤ (c ^ p * C) ^ (1 / p) := by gcongr
    _ = c * C ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp.ne', ENNReal.rpow_one]

end Lp

/-- **Lemma `lem:gauss`**, `L^p` form: if `X ∼ N(0, v)` then `‖X‖_p = √v ‖N‖_p`, `N ∼ N(0, 1)`. -/
theorem eLpNorm_of_hasLaw_gaussianReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {v : ℝ≥0} (hX : HasLaw X (gaussianReal 0 v) P) (p : ℝ≥0∞) :
    eLpNorm X p P =
      ENNReal.ofReal (Real.sqrt v) * eLpNorm (id : ℝ → ℝ) p (gaussianReal 0 1) := by
  have h1 : eLpNorm X p P = eLpNorm (id : ℝ → ℝ) p (P.map X) :=
    (eLpNorm_map_measure aestronglyMeasurable_id hX.aemeasurable).symm
  have hm : Measurable fun x : ℝ => Real.sqrt v * x := measurable_const.mul measurable_id
  rw [h1, hX.map_eq, gaussianReal_eq_map_sqrt_mul,
    eLpNorm_map_measure aestronglyMeasurable_id hm.aemeasurable]
  have h2 : (id ∘ fun x : ℝ => Real.sqrt v * x) = Real.sqrt v • (id : ℝ → ℝ) := by
    funext x
    simp only [Function.comp_apply, id_eq, Pi.smul_apply, smul_eq_mul]
  rw [h2, eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]

end GaussianLQG
