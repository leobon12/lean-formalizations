import InteractingSLE.Spec.Ito.ACChain
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Wang–Wu at `κ = 4`: force images are determined by the driver (Lemma 2.1, pathwise uniqueness)

Packet PROVE-WW-A. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §2, Lemma 2.1, first paragraph of
the proof (ruling R31): "For the same side and initial value, let `V, V′` be two continuous, locally absolutely
continuous ordered solutions for the same driver. Outside their collision-time null sets,
`d/dt (V − V′)² = −4(V − V′)²/((V − W)(V′ − W)) ≤ 0`. The square is locally absolutely continuous, so equality at
time zero implies equality everywhere."

* `forceImage_unique`: two solutions `v, v'` of `v t = x + ∫₀ᵗ 2/(v − w)` on `[0, T]` on the same side of the driver
  (both `≤ w` or both `≥ w`), with integrable reciprocal gaps and null collision sets, coincide on `[0, T]`.

The Lean proof uses the chain rule for absolutely continuous paths (`Ito.comp_eq_add_integral_of_lipschitz`) with the
Lipschitz `C¹` function `Φ(x) = √(x² + 1)` instead of `x²`: `Φ(D_t) − 1 = ∫ D g/√(D² + 1) ≤ 0` for
`D = v − v'`, `g = 2/(v − w) − 2/(v' − w)`, since `D g = −2D²/((v − w)(v' − w)) ≤ 0` off the collisions.

Not done here: the Borel reconstruction map (Lusin–Souslin) and the identification with the geometric images (the
rest of Lemma 2.1).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal

namespace InteractingSLE

namespace WangWu

/-- `Φ(x) = √(x² + 1)`, a Lipschitz `C¹` substitute for `x²`. -/
def sqrtOneAddSq (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + 1)

theorem hasDerivAt_sqrtOneAddSq (x : ℝ) :
    HasDerivAt sqrtOneAddSq (x / Real.sqrt (x ^ 2 + 1)) x := by
  have hpos : (0 : ℝ) < x ^ 2 + 1 := by positivity
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 + 1) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const 1
  have h2 := h1.sqrt hpos.ne'
  have e : 2 * x / (2 * Real.sqrt (x ^ 2 + 1)) = x / Real.sqrt (x ^ 2 + 1) :=
    mul_div_mul_left _ _ two_ne_zero
  rw [e] at h2
  exact h2

theorem abs_deriv_sqrtOneAddSq_le (x : ℝ) : |x / Real.sqrt (x ^ 2 + 1)| ≤ 1 := by
  have hpos : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  rw [abs_div, abs_of_pos hpos, div_le_one hpos]
  calc |x| = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
    _ ≤ Real.sqrt (x ^ 2 + 1) := Real.sqrt_le_sqrt (by linarith)

theorem lipschitzWith_sqrtOneAddSq : LipschitzWith 1 sqrtOneAddSq := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_sqrtOneAddSq x).differentiableAt)
    fun x => ?_
  rw [(hasDerivAt_sqrtOneAddSq x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact abs_deriv_sqrtOneAddSq_le x

theorem continuous_deriv_sqrtOneAddSq : Continuous fun x : ℝ => x / Real.sqrt (x ^ 2 + 1) :=
  continuous_id.div (Real.continuous_sqrt.comp ((continuous_pow 2).add continuous_const))
    fun x => (Real.sqrt_pos.2 (by positivity)).ne'

/-- **Lemma 2.1, pathwise uniqueness.** Two integral solutions `v, v'` of `v t = x + ∫₀ᵗ 2/(v − w)` on `[0, T]`, on the
same side of the driver `w`, with integrable reciprocal gaps and Lebesgue-null collision sets, coincide on `[0, T]`. -/
theorem forceImage_unique {w v v' : ℝ → ℝ} {x T : ℝ} (hT : 0 ≤ T)
    (hside : (∀ s ∈ Icc 0 T, v s ≤ w s ∧ v' s ≤ w s) ∨ ∀ s ∈ Icc 0 T, w s ≤ v s ∧ w s ≤ v' s)
    (hint : IntervalIntegrable (fun s => (v s - w s)⁻¹) volume 0 T)
    (hint' : IntervalIntegrable (fun s => (v' s - w s)⁻¹) volume 0 T)
    (hv : ∀ t ∈ Icc 0 T, v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s - w s))
    (hv' : ∀ t ∈ Icc 0 T, v' t = x + ∫ s in (0 : ℝ)..t, 2 / (v' s - w s))
    (hnull : volume {s | s ∈ Icc 0 T ∧ v s = w s} = 0)
    (hnull' : volume {s | s ∈ Icc 0 T ∧ v' s = w s} = 0) :
    ∀ t ∈ Icc 0 T, v t = v' t := by
  intro t ht
  set g : ℝ → ℝ := fun s => 2 / (v s - w s) - 2 / (v' s - w s) with hgdef
  have hint2 : ∀ {u : ℝ → ℝ}, IntervalIntegrable (fun s => (u s - w s)⁻¹) volume 0 T →
      IntervalIntegrable (fun s => 2 / (u s - w s)) volume 0 T := fun h => by
    simpa [div_eq_mul_inv] using h.const_mul 2
  have hgi : IntervalIntegrable g volume 0 T := (hint2 hint).sub (hint2 hint')
  have hgit : IntervalIntegrable g volume 0 t :=
    hgi.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc_right ht.2)
  set D : ℝ → ℝ := fun s => v s - v' s with hDdef
  have hD : ∀ r ∈ uIcc 0 t, D r = D 0 + ∫ s in (0 : ℝ)..r, g s := by
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have hgr : IntervalIntegrable (fun s => 2 / (v s - w s)) volume 0 r :=
      (hint2 hint).mono_set (by rw [uIcc_of_le hr.1, uIcc_of_le hT]; exact Icc_subset_Icc_right hrT.2)
    have hgr' : IntervalIntegrable (fun s => 2 / (v' s - w s)) volume 0 r :=
      (hint2 hint').mono_set (by rw [uIcc_of_le hr.1, uIcc_of_le hT]; exact Icc_subset_Icc_right hrT.2)
    simp only [hDdef, hgdef]
    rw [hv r hrT, hv' r hrT, hv 0 h0, hv' 0 h0, intervalIntegral.integral_sub hgr hgr']
    simp
  have hchain := Ito.comp_eq_add_integral_of_lipschitz (E := ℝ) (Φ := sqrtOneAddSq)
    (Φ' := fun y => (y / Real.sqrt (y ^ 2 + 1)) • ContinuousLinearMap.id ℝ ℝ)
    (fun y => (hasDerivAt_sqrtOneAddSq y).hasFDerivAt.congr_fderiv (by ext; simp))
    lipschitzWith_sqrtOneAddSq
    ((continuous_deriv_sqrtOneAddSq).smul continuous_const) hgit hD
  have hD0 : D 0 = 0 := by
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    simp only [hDdef, hv 0 h0, hv' 0 h0, intervalIntegral.integral_same, add_zero, sub_self]
  -- the integrand is nonpositive almost everywhere
  have hneg : ∀ᵐ s ∂volume, s ∈ Icc (0 : ℝ) t →
      (fun y => (y / Real.sqrt (y ^ 2 + 1)) • ContinuousLinearMap.id ℝ ℝ) (D s) (g s) ≤ 0 := by
    have hn : volume ({s | s ∈ Icc 0 T ∧ v s = w s} ∪ {s | s ∈ Icc 0 T ∧ v' s = w s}) = 0 :=
      measure_union_null hnull hnull'
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hn] with s hs hsI
    have hsT : s ∈ Icc 0 T := ⟨hsI.1, hsI.2.trans ht.2⟩
    simp only [mem_union, mem_ofPred_eq, not_or, not_and] at hs
    have ha : v s - w s ≠ 0 := sub_ne_zero.2 (hs.1 hsT)
    have hb : v' s - w s ≠ 0 := sub_ne_zero.2 (hs.2 hsT)
    have hab : 0 < (v s - w s) * (v' s - w s) := by
      rcases hside with h | h
      · have h1 := (h s hsT).1; have h2 := (h s hsT).2
        have : v s - w s < 0 := lt_of_le_of_ne (by linarith) ha
        have : v' s - w s < 0 := lt_of_le_of_ne (by linarith) hb
        nlinarith
      · have h1 := (h s hsT).1; have h2 := (h s hsT).2
        have : 0 < v s - w s := lt_of_le_of_ne (by linarith) (Ne.symm ha)
        have : 0 < v' s - w s := lt_of_le_of_ne (by linarith) (Ne.symm hb)
        positivity
    have hDg : D s * g s = -2 * D s ^ 2 / ((v s - w s) * (v' s - w s)) := by
      simp only [hDdef, hgdef]
      field_simp
      ring
    have hDg0 : D s * g s ≤ 0 := by
      rw [hDg]
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (D s)]) hab.le
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div]
    exact div_nonpos_of_nonpos_of_nonneg hDg0 (Real.sqrt_nonneg _)
  have hint0 : ∫ s in (0 : ℝ)..t,
      (fun y => (y / Real.sqrt (y ^ 2 + 1)) • ContinuousLinearMap.id ℝ ℝ) (D s) (g s) ≤ 0 :=
    by
      have h0 := intervalIntegral.integral_nonneg_of_ae_restrict ht.1
        (f := fun s => -((fun y => (y / Real.sqrt (y ^ 2 + 1)) • ContinuousLinearMap.id ℝ ℝ) (D s) (g s)))
        ((ae_restrict_iff' measurableSet_Icc).2 (hneg.mono fun s h hs => neg_nonneg.2 (h hs)))
      rw [intervalIntegral.integral_neg] at h0
      linarith
  rw [hD0] at hchain
  have hle : sqrtOneAddSq (D t) ≤ 1 := by
    rw [hchain]
    simp only [sqrtOneAddSq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add,
      Real.sqrt_one]
    linarith
  have hsq : D t ^ 2 ≤ 0 := by
    have h1 : Real.sqrt (D t ^ 2 + 1) ≤ Real.sqrt 1 := by rw [Real.sqrt_one]; exact hle
    have h2 := (Real.sqrt_le_sqrt_iff (by norm_num : (0 : ℝ) ≤ 1)).1 h1
    linarith
  have : D t = 0 := by nlinarith [sq_nonneg (D t)]
  simp only [hDdef] at this
  linarith

end WangWu

end InteractingSLE
