/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.OneForceLip
import InteractingSLE.Spec.Zhan.ConstDriftGapScale
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# A.3.2: the upper-point flow is a differentiable increasing bijection, `∂_u X_t(u) = exp ∫₀ᵗ ½ sech²(X/2)`

Packet PROVE-ZHAN-A32. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L653–L693, ruling R38):

> For the upper-point flow `X_t(u) = Re ψ_t(u + iπ) − ξ_t`, `dX_t = −√κ dB_t + [tanh(X_t/2) − σ] dt`, one has
> `∂_t ∂_u X_t = ½ sech²(X_t/2) ∂_u X_t` … `∂_u X_t ≤ e^{t/2}` … The map `u ↦ X_t(u)` is an increasing bijection of
> `ℝ`, so `∫_ℝ M_t(u) du = 1`.

This file is the deterministic half, for an arbitrary continuous strip driver path `ξ` (no probability). The
upper-point flow is the global solution of (3.15) in integrated form (PROVE-ZHAN-A's `IsSepMark.upperGap_eq`),

  `X_t(u) = u − ξ_t + ∫₀ᵗ tanh(X_s(u)/2) ds`                                                  (`upFlow`)

(`OneForce.lipSol`: `tanh(·/2)` is `½`-Lipschitz and bounded). Note `½ sech²(x/2) = 1/(1 + cosh x)` (`sechHalf`).

## Main results

* `upFlow_sub_eq`: **the exact linear relation** `X_t(u') − X_t(u) = (u' − u) exp ∫₀ᵗ q_s`, with
  `q_s = ∫₀¹ ½ sech²((X_s(u) + r(X_s(u') − X_s(u)))/2) dr ∈ [0, ½]` the divided difference of `tanh(·/2)`;
* `hasDerivAt_upFlow`: **`∂_u X_t(u) = upDeriv ξ u t = exp ∫₀ᵗ ½ sech²(X_s(u)/2) ds`**, with
  `1 ≤ upDeriv ≤ e^{t/2}` (`one_le_upDeriv`, `upDeriv_le`);
* `strictMono_upFlow`, `surjective_upFlow`: `u ↦ X_t(u)` is an increasing bijection of `ℝ`;
* `lintegral_upDeriv_mul_comp`: **the change of variables** `∫ ∂_u X_t(u) g(X_t(u)) du = ∫ g(x) dx` for every
  `g : ℝ → ℝ≥0∞` (the source's `∫_ℝ M_t(u) du = 1` when `g` is the mixture density).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.Mix

/-! ### `½ sech²(x/2) = 1/(1 + cosh x)` and the divided difference of `tanh(·/2)` -/

/-- `½ sech²(x/2) = 1/(1 + cosh x)`, the derivative of `tanh(x/2)`. -/
def sechHalf (x : ℝ) : ℝ := (1 + Real.cosh x)⁻¹

theorem one_add_cosh_pos (x : ℝ) : 0 < 1 + Real.cosh x := by
  have := Real.cosh_pos x; linarith

theorem one_add_cosh_eq (x : ℝ) : 1 + Real.cosh x = 2 * Real.cosh (x / 2) ^ 2 := by
  have h1 := Real.cosh_two_mul (x / 2)
  have h2 := Real.cosh_sq_sub_sinh_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h1
  rw [h1]; linarith

theorem sechHalf_pos (x : ℝ) : 0 < sechHalf x := inv_pos.2 (one_add_cosh_pos x)

theorem sechHalf_le (x : ℝ) : sechHalf x ≤ 1 / 2 := by
  rw [sechHalf, ← one_div, div_le_div_iff₀ (one_add_cosh_pos x) two_pos]
  linarith [Real.one_le_cosh x]

theorem continuous_sechHalf : Continuous sechHalf :=
  (continuous_const.add Real.continuous_cosh).inv₀ fun x => (one_add_cosh_pos x).ne'

theorem hasDerivAt_tanh_half (x : ℝ) : HasDerivAt (fun x => Real.tanh (x / 2)) (sechHalf x) x := by
  have h2 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) x := by
    simpa using (hasDerivAt_id x).div_const 2
  refine ((Zhan.hasDerivAt_tanh (x / 2)).comp x h2).congr_deriv ?_
  rw [sechHalf, one_add_cosh_eq]
  have := Real.cosh_pos (x / 2)
  field_simp

theorem hasDerivAt_sechHalf (x : ℝ) :
    HasDerivAt sechHalf (-Real.sinh x / (1 + Real.cosh x) ^ 2) x :=
  ((Real.hasDerivAt_cosh x).const_add 1).inv (one_add_cosh_pos x).ne'

/-- `|(1/(1 + cosh x))'| ≤ 1/4`. -/
theorem abs_deriv_sechHalf_le (x : ℝ) : |-Real.sinh x / (1 + Real.cosh x) ^ 2| ≤ 1 / 4 := by
  have hc := Real.cosh_pos x
  have hs : |Real.sinh x| ≤ Real.cosh x := by
    rw [← abs_of_pos hc]
    exact sq_le_sq.1 (by nlinarith [Real.cosh_sq_sub_sinh_sq x])
  rw [abs_div, abs_neg, abs_of_pos (pow_pos (one_add_cosh_pos x) 2),
    div_le_iff₀ (pow_pos (one_add_cosh_pos x) 2)]
  nlinarith [sq_nonneg (Real.cosh x - 1)]

theorem lipschitzWith_sechHalf : LipschitzWith (1 / 4 : ℝ≥0) sechHalf := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_sechHalf x).differentiableAt) fun x => ?_
  rw [(hasDerivAt_sechHalf x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  push_cast
  exact abs_deriv_sechHalf_le x

/-- **The divided difference of `tanh(·/2)`**: `q(a, b) = ∫₀¹ ½ sech²((a + r(b − a))/2) dr`. -/
@[irreducible] def tanhSlope (a b : ℝ) : ℝ := ∫ r in (0 : ℝ)..1, sechHalf (a + r * (b - a))

theorem tanh_half_sub (a b : ℝ) :
    Real.tanh (b / 2) - Real.tanh (a / 2) = tanhSlope a b * (b - a) := by
  have hd : ∀ r ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r => Real.tanh ((a + r * (b - a)) / 2))
      (sechHalf (a + r * (b - a)) * (b - a)) r := fun r _ => by
    have hin : HasDerivAt (fun r : ℝ => a + r * (b - a)) (b - a) r := by
      simpa using ((hasDerivAt_id r).mul_const (b - a)).const_add a
    exact (hasDerivAt_tanh_half (a + r * (b - a))).comp r hin
  have hint : IntervalIntegrable (fun r => sechHalf (a + r * (b - a)) * (b - a)) volume 0 1 :=
    ((continuous_sechHalf.comp (by fun_prop : Continuous fun r : ℝ => a + r * (b - a))).mul
      continuous_const).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_mul_const] at h
  simp only [one_mul, zero_mul, add_zero, add_sub_cancel] at h
  rw [tanhSlope, h]

theorem tanhSlope_nonneg (a b : ℝ) : 0 ≤ tanhSlope a b := by
  unfold tanhSlope
  exact intervalIntegral.integral_nonneg zero_le_one fun _ _ => (sechHalf_pos _).le

theorem tanhSlope_le (a b : ℝ) : tanhSlope a b ≤ 1 / 2 := by
  have h := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    ((continuous_sechHalf.comp (by fun_prop : Continuous fun r : ℝ => a + r * (b - a))).intervalIntegrable 0 1)
    (intervalIntegrable_const (c := (1 / 2 : ℝ))) fun r _ => sechHalf_le (a + r * (b - a))
  simpa [tanhSlope] using h

theorem abs_tanhSlope_sub_le (a b : ℝ) : |tanhSlope a b - sechHalf a| ≤ |b - a| / 4 := by
  have hc : Continuous fun r : ℝ => sechHalf (a + r * (b - a)) :=
    continuous_sechHalf.comp (by fun_prop)
  have e : tanhSlope a b - sechHalf a = ∫ r in (0 : ℝ)..1, (sechHalf (a + r * (b - a)) - sechHalf a) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable 0 1) intervalIntegrable_const,
      intervalIntegral.integral_const, tanhSlope]
    simp
  rw [e]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := |b - a| / 4)
    (f := fun r => sechHalf (a + r * (b - a)) - sechHalf a) fun r hr => by
      rw [uIoc_of_le zero_le_one] at hr
      have hl := lipschitzWith_sechHalf.dist_le_mul (a + r * (b - a)) a
      rw [Real.dist_eq, Real.dist_eq, add_sub_cancel_left, abs_mul, abs_of_pos hr.1] at hl
      rw [Real.norm_eq_abs]
      refine hl.trans ?_
      push_cast
      nlinarith [abs_nonneg (b - a), hr.2]
  simpa using h

theorem continuous_tanhSlope : Continuous fun p : ℝ × ℝ => tanhSlope p.1 p.2 := by
  unfold tanhSlope
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℝ × ℝ) (r : ℝ) => sechHalf (p.1 + r * (p.2 - p.1)))
    (continuous_sechHalf.comp (by fun_prop)) 0 1

/-! ### The upper-point flow -/

/-- **The upper-point flow** `X_t(u) = u − ξ_t + ∫₀ᵗ tanh(X_s(u)/2) ds` (the global solution `OneForce.lipSol`). -/
@[irreducible] def upFlow (ξ : ℝ → ℝ) (u t : ℝ) : ℝ :=
  OneForce.lipSol (fun x => Real.tanh (x / 2)) u (fun s => -ξ s) t

/-- **The `u`-derivative of the flow**, `∂_u X_t(u) = exp ∫₀ᵗ ½ sech²(X_s(u)/2) ds`. -/
def upDeriv (ξ : ℝ → ℝ) (u t : ℝ) : ℝ := Real.exp (∫ s in (0 : ℝ)..t, sechHalf (upFlow ξ u s))

variable {ξ : ℝ → ℝ}

theorem lipData_tanh (hξ : Continuous ξ) : OneForce.LipData (fun x => Real.tanh (x / 2)) (fun s => -ξ s) :=
  ⟨⟨_, Zhan.lipschitzWith_tanh_half⟩, ⟨1, fun _ => (Real.abs_tanh_lt_one _).le⟩, hξ.neg⟩

theorem upFlow_eq (hξ : Continuous ξ) (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    upFlow ξ u t = u - ξ t + ∫ s in (0 : ℝ)..t, Real.tanh (upFlow ξ u s / 2) := by
  simp only [upFlow]
  rw [OneForce.lipSol_eq (lipData_tanh hξ) u ht]
  ring

theorem upFlow_zero (hξ : Continuous ξ) (hξ0 : ξ 0 = 0) (u : ℝ) : upFlow ξ u 0 = u := by
  rw [upFlow_eq hξ u le_rfl, hξ0, intervalIntegral.integral_same]; ring

theorem continuousOn_upFlow (hξ : Continuous ξ) (u : ℝ) : ContinuousOn (upFlow ξ u) (Ici 0) := by
  unfold upFlow
  exact OneForce.continuousOn_lipSol_Ici (lipData_tanh hξ) u

/-- The flow read through `max · 0`: continuous on all of `ℝ`. -/
theorem continuous_tanh_half : Continuous fun x : ℝ => Real.tanh (x / 2) :=
  Zhan.lipschitzWith_tanh_half.continuous

theorem continuous_upFlow_max (hξ : Continuous ξ) (u : ℝ) : Continuous fun s => upFlow ξ u (max s 0) :=
  (continuousOn_upFlow hξ u).comp_continuous (continuous_id.max continuous_const) fun s => le_max_right s 0

theorem abs_integral_tanh_le {f : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    |∫ s in (0 : ℝ)..t, Real.tanh (f s / 2)| ≤ t := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
    (f := fun s => Real.tanh (f s / 2)) fun s _ => by
      rw [Real.norm_eq_abs]; exact (Real.abs_tanh_lt_one _).le
  simpa [abs_of_nonneg ht] using h

/-- `|X_t(u) − (u − ξ_t)| ≤ t`. -/
theorem abs_upFlow_sub_self_le (hξ : Continuous ξ) (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |upFlow ξ u t - (u - ξ t)| ≤ t := by
  have h := upFlow_eq hξ u ht
  have h2 := abs_integral_tanh_le (f := upFlow ξ u) ht
  set I := ∫ s in (0 : ℝ)..t, Real.tanh (upFlow ξ u s / 2)
  rw [show upFlow ξ u t - (u - ξ t) = I by linarith]
  exact h2

/-! ### The exact linear relation between two initial points -/

/-- The integrated divided difference `∫₀ᵗ q(X_s(u), X_s(u')) ds`. -/
def slopeInt (ξ : ℝ → ℝ) (u u' t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, tanhSlope (upFlow ξ u s) (upFlow ξ u' s)

theorem slopeInt_nonneg (u u' : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ slopeInt ξ u u' t :=
  intervalIntegral.integral_nonneg ht fun _ _ => tanhSlope_nonneg _ _

theorem slopeInt_le (hξ : Continuous ξ) (u u' : ℝ) {t : ℝ} (ht : 0 ≤ t) : slopeInt ξ u u' t ≤ t / 2 := by
  have hc : ContinuousOn (fun s => tanhSlope (upFlow ξ u s) (upFlow ξ u' s)) (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact continuous_tanhSlope.comp_continuousOn
      (((continuousOn_upFlow hξ u).mono Icc_subset_Ici_self).prodMk
        ((continuousOn_upFlow hξ u').mono Icc_subset_Ici_self))
  have h := intervalIntegral.integral_mono_on (μ := volume) ht hc.intervalIntegrable
    (intervalIntegrable_const (c := (1 / 2 : ℝ))) fun s _ => tanhSlope_le _ _
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  unfold slopeInt; linarith

/-- **`X_t(u') − X_t(u) = (u' − u) exp ∫₀ᵗ q_s`.** -/
theorem upFlow_sub_eq (hξ : Continuous ξ) (u u' : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    upFlow ξ u' t - upFlow ξ u t = (u' - u) * Real.exp (slopeInt ξ u u' t) := by
  set X : ℝ → ℝ := fun s => upFlow ξ u (max s 0) with hX
  set X' : ℝ → ℝ := fun s => upFlow ξ u' (max s 0) with hX'
  have hXc : Continuous X := continuous_upFlow_max hξ u
  have hXc' : Continuous X' := continuous_upFlow_max hξ u'
  set g : ℝ → ℝ := fun s => Real.tanh (X' s / 2) - Real.tanh (X s / 2) with hg
  have hgc : Continuous g := (continuous_tanh_half.comp hXc').sub (continuous_tanh_half.comp hXc)
  set q : ℝ → ℝ := fun s => tanhSlope (X s) (X' s) with hq
  have hqc : Continuous q := continuous_tanhSlope.comp (hXc.prodMk hXc')
  set D : ℝ → ℝ := fun s => (u' - u) + ∫ r in (0 : ℝ)..s, g r with hD
  set Q : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, q r with hQ
  have hDd : ∀ s, HasDerivAt D (g s) s := fun s => ((hgc.integral_hasStrictDerivAt 0 s).hasDerivAt).const_add _
  have hQd : ∀ s, HasDerivAt Q (q s) s := fun s => (hqc.integral_hasStrictDerivAt 0 s).hasDerivAt
  -- `D` is the difference of the flows on `[0, ∞)`
  have hint : ∀ {s : ℝ}, 0 ≤ s → ∀ v : ℝ,
      ∫ r in (0 : ℝ)..s, Real.tanh (upFlow ξ v r / 2) = ∫ r in (0 : ℝ)..s, Real.tanh (upFlow ξ v (max r 0) / 2) :=
    fun {s} hs v => intervalIntegral.integral_congr fun r hr => by
      rw [uIcc_of_le hs] at hr
      simp only [max_eq_left hr.1]
  have hDeq : ∀ {s : ℝ}, 0 ≤ s → D s = upFlow ξ u' s - upFlow ξ u s := fun {s} hs => by
    have hi1 : IntervalIntegrable (fun r => Real.tanh (X' r / 2)) volume 0 s :=
      (continuous_tanh_half.comp hXc').intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun r => Real.tanh (X r / 2)) volume 0 s :=
      (continuous_tanh_half.comp hXc).intervalIntegrable _ _
    simp only [hD, hg]
    rw [intervalIntegral.integral_sub hi1 hi2, upFlow_eq hξ u' hs, upFlow_eq hξ u hs, hint hs u, hint hs u']
    ring
  have hgq : ∀ {s : ℝ}, 0 ≤ s → g s = q s * D s := fun {s} hs => by
    simp only [hg, hq]
    rw [tanh_half_sub, hDeq hs]
    simp only [hX, hX', max_eq_left hs]
  -- `D e^{−Q}` is constant on `[0, t]`
  set h : ℝ → ℝ := fun s => D s * Real.exp (-Q s) with hh
  set h' : ℝ → ℝ := fun s => (g s - q s * D s) * Real.exp (-Q s) with hh'
  have hhd : ∀ s, HasDerivAt h (h' s) s := fun s => by
    have := (hDd s).mul ((hQd s).neg.exp)
    refine this.congr_deriv ?_
    simp only [hh', Pi.neg_apply]; ring
  have hcD : Continuous D := continuous_iff_continuousAt.2 fun s => (hDd s).continuousAt
  have hcQ : Continuous Q := continuous_iff_continuousAt.2 fun s => (hQd s).continuousAt
  have hc' : Continuous h' := ((hgc.sub (hqc.mul hcD)).mul (Real.continuous_exp.comp hcQ.neg))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hhd s) (hc'.intervalIntegrable 0 t)
  have hzero : ∫ s in (0 : ℝ)..t, h' s = 0 := by
    have e : ∫ s in (0 : ℝ)..t, h' s = ∫ _ in (0 : ℝ)..t, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht] at hs
      simp only [hh', hgq hs.1, sub_self, zero_mul]
    rw [e, intervalIntegral.integral_zero]
  rw [hzero] at hFTC
  have h0 : h 0 = u' - u := by simp [hh, hD, hQ]
  have hQt : Q t = slopeInt ξ u u' t := by
    simp only [hQ, hq, slopeInt]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht] at hr
    simp only [hX, hX', max_eq_left hr.1]
  have hht : h t = u' - u := by linarith
  rw [← hDeq ht, ← hQt]
  simp only [hh] at hht
  calc D t = D t * Real.exp (-Q t) * Real.exp (Q t) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = (u' - u) * Real.exp (Q t) := by rw [hht]

theorem upFlow_lt_upFlow (hξ : Continuous ξ) {u u' : ℝ} (huu : u < u') {t : ℝ} (ht : 0 ≤ t) :
    upFlow ξ u t < upFlow ξ u' t := by
  have h := upFlow_sub_eq hξ u u' ht
  have : 0 < (u' - u) * Real.exp (slopeInt ξ u u' t) := mul_pos (by linarith) (Real.exp_pos _)
  linarith

theorem strictMono_upFlow (hξ : Continuous ξ) {t : ℝ} (ht : 0 ≤ t) : StrictMono fun u => upFlow ξ u t :=
  fun _ _ huu => upFlow_lt_upFlow hξ huu ht

/-- `|X_t(u') − X_t(u)| ≤ e^{t/2} |u' − u|`. -/
theorem abs_upFlow_sub_le (hξ : Continuous ξ) (u u' : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |upFlow ξ u' t - upFlow ξ u t| ≤ Real.exp (t / 2) * |u' - u| := by
  rw [upFlow_sub_eq hξ u u' ht, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (slopeInt_le hξ u u' ht)) (abs_nonneg _)

theorem continuous_upFlow_initial (hξ : Continuous ξ) {t : ℝ} (ht : 0 ≤ t) : Continuous fun u => upFlow ξ u t := by
  refine Metric.continuous_iff.2 fun u ε hε => ⟨ε / Real.exp (t / 2), div_pos hε (Real.exp_pos _), fun u' hu' => ?_⟩
  rw [Real.dist_eq] at hu' ⊢
  calc |upFlow ξ u' t - upFlow ξ u t| ≤ Real.exp (t / 2) * |u' - u| := abs_upFlow_sub_le hξ u u' ht
    _ < Real.exp (t / 2) * (ε / Real.exp (t / 2)) := mul_lt_mul_of_pos_left hu' (Real.exp_pos _)
    _ = ε := by field_simp

/-! ### The derivative in the initial point -/

theorem one_le_upDeriv (u : ℝ) {t : ℝ} (ht : 0 ≤ t) : 1 ≤ upDeriv ξ u t :=
  Real.one_le_exp_iff.2 (intervalIntegral.integral_nonneg ht fun _ _ => (sechHalf_pos _).le)

theorem upDeriv_pos (u t : ℝ) : 0 < upDeriv ξ u t := Real.exp_pos _

theorem upDeriv_le (hξ : Continuous ξ) (u : ℝ) {t : ℝ} (ht : 0 ≤ t) : upDeriv ξ u t ≤ Real.exp (t / 2) := by
  refine Real.exp_le_exp.2 ?_
  have hc : ContinuousOn (fun s => sechHalf (upFlow ξ u s)) (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact continuous_sechHalf.comp_continuousOn ((continuousOn_upFlow hξ u).mono Icc_subset_Ici_self)
  have h := intervalIntegral.integral_mono_on (μ := volume) ht hc.intervalIntegrable
    (intervalIntegrable_const (c := (1 / 2 : ℝ))) fun s _ => sechHalf_le _
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  linarith

/-- `|∫₀ᵗ q(X_s(u), X_s(u')) − ∫₀ᵗ ½ sech²(X_s(u)/2)| ≤ t e^{t/2} |u' − u| / 4`. -/
theorem abs_slopeInt_sub_le (hξ : Continuous ξ) (u u' : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    |slopeInt ξ u u' t - ∫ s in (0 : ℝ)..t, sechHalf (upFlow ξ u s)| ≤
      Real.exp (t / 2) * |u' - u| / 4 * t := by
  have hc1 : ContinuousOn (fun s => tanhSlope (upFlow ξ u s) (upFlow ξ u' s)) (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact continuous_tanhSlope.comp_continuousOn
      (((continuousOn_upFlow hξ u).mono Icc_subset_Ici_self).prodMk
        ((continuousOn_upFlow hξ u').mono Icc_subset_Ici_self))
  have hc2 : ContinuousOn (fun s => sechHalf (upFlow ξ u s)) (uIcc 0 t) := by
    rw [uIcc_of_le ht]
    exact continuous_sechHalf.comp_continuousOn ((continuousOn_upFlow hξ u).mono Icc_subset_Ici_self)
  rw [slopeInt, ← intervalIntegral.integral_sub hc1.intervalIntegrable hc2.intervalIntegrable]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (C := Real.exp (t / 2) * |u' - u| / 4)
    (f := fun s => tanhSlope (upFlow ξ u s) (upFlow ξ u' s) - sechHalf (upFlow ξ u s)) fun s hs => by
      rw [uIoc_of_le ht] at hs
      rw [Real.norm_eq_abs]
      refine (abs_tanhSlope_sub_le _ _).trans ?_
      have h1 := abs_upFlow_sub_le hξ u u' hs.1.le
      have h2 : Real.exp (s / 2) ≤ Real.exp (t / 2) := Real.exp_le_exp.2 (by linarith [hs.2])
      have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (u' - u))
      linarith
  simpa [abs_of_nonneg ht] using h

/-- **`∂_u X_t(u) = exp ∫₀ᵗ ½ sech²(X_s(u)/2) ds`.** -/
theorem hasDerivAt_upFlow (hξ : Continuous ξ) (u : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => upFlow ξ u t) (upDeriv ξ u t) u := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : slope (fun u => upFlow ξ u t) u =ᶠ[𝓝[≠] u] fun u' => Real.exp (slopeInt ξ u u' t) := by
    filter_upwards [self_mem_nhdsWithin] with u' hu'
    have hne : u' - u ≠ 0 := sub_ne_zero.2 hu'
    rw [slope_def_field, upFlow_sub_eq hξ u u' ht]
    field_simp
  refine Tendsto.congr' hslope.symm ?_
  refine (Real.continuous_exp.tendsto _).comp (tendsto_nhdsWithin_of_tendsto_nhds ?_)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun u' => Real.exp (t / 2) * |u' - u| / 4 * t) (𝓝 u) (𝓝 0) := by
    have : Continuous fun u' : ℝ => Real.exp (t / 2) * |u' - u| / 4 * t := by fun_prop
    simpa using this.tendsto u
  refine squeeze_zero (fun _ => norm_nonneg _) (fun u' => ?_) hb
  rw [Real.norm_eq_abs]
  exact abs_slopeInt_sub_le hξ u u' ht

/-- `u ↦ ∂_u X_t(u)` is continuous (`½ sech²(·/2)` is `¼`-Lipschitz and `|X_s(u') − X_s(u)| ≤ e^{s/2}|u' − u|`). -/
theorem continuous_upDeriv_initial (hξ : Continuous ξ) {t : ℝ} (ht : 0 ≤ t) : Continuous fun u => upDeriv ξ u t := by
  have hc : ∀ u, ContinuousOn (fun s => sechHalf (upFlow ξ u s)) (uIcc 0 t) := fun u => by
    rw [uIcc_of_le ht]
    exact continuous_sechHalf.comp_continuousOn ((continuousOn_upFlow hξ u).mono Icc_subset_Ici_self)
  have hL : LipschitzWith (Real.toNNReal (Real.exp (t / 2) / 4 * t))
      fun u => ∫ s in (0 : ℝ)..t, sechHalf (upFlow ξ u s) := by
    refine LipschitzWith.of_dist_le' fun u' u => ?_
    rw [Real.dist_eq, Real.dist_eq, ← intervalIntegral.integral_sub (hc u').intervalIntegrable
      (hc u).intervalIntegrable]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := Real.exp (t / 2) / 4 * |u' - u|)
      (f := fun s => sechHalf (upFlow ξ u' s) - sechHalf (upFlow ξ u s)) fun s hs => by
        rw [uIoc_of_le ht] at hs
        rw [Real.norm_eq_abs]
        have hl := lipschitzWith_sechHalf.dist_le_mul (upFlow ξ u' s) (upFlow ξ u s)
        rw [Real.dist_eq, Real.dist_eq] at hl
        have h1 := abs_upFlow_sub_le hξ u u' hs.1.le
        have h2 : Real.exp (s / 2) ≤ Real.exp (t / 2) := Real.exp_le_exp.2 (by linarith [hs.2])
        have h3 := mul_le_mul_of_nonneg_right h2 (abs_nonneg (u' - u))
        push_cast at hl
        nlinarith [abs_nonneg (u' - u)]
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] at h
    calc _ ≤ Real.exp (t / 2) / 4 * |u' - u| * t := h
      _ = Real.exp (t / 2) / 4 * t * |u' - u| := by ring
  exact Real.continuous_exp.comp hL.continuous

/-! ### Bijectivity and the change of variables -/

theorem surjective_upFlow (hξ : Continuous ξ) {t : ℝ} (ht : 0 ≤ t) : Function.Surjective fun u => upFlow ξ u t := by
  intro y
  set u₁ := y + ξ t - t - 1
  set u₂ := y + ξ t + t + 1
  have h₁ : upFlow ξ u₁ t ≤ y := by
    have := abs_upFlow_sub_self_le hξ u₁ ht
    linarith [(abs_le.1 this).2]
  have h₂ : y ≤ upFlow ξ u₂ t := by
    have := abs_upFlow_sub_self_le hξ u₂ ht
    linarith [(abs_le.1 this).1]
  have h12 : u₁ ≤ u₂ := by simp only [u₁, u₂]; linarith
  obtain ⟨u, -, hu⟩ := intermediate_value_Icc h12 (continuous_upFlow_initial hξ ht).continuousOn ⟨h₁, h₂⟩
  exact ⟨u, hu⟩

/-- **The change of variables** `u ↦ X_t(u)`: `∫ ∂_u X_t(u) · g(X_t(u)) du = ∫ g(x) dx`. -/
theorem lintegral_upDeriv_mul_comp (hξ : Continuous ξ) {t : ℝ} (ht : 0 ≤ t) (g : ℝ → ℝ≥0∞) :
    ∫⁻ u, ENNReal.ofReal (upDeriv ξ u t) * g (upFlow ξ u t) = ∫⁻ x, g x := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := univ) (f := fun u => upFlow ξ u t)
    (f' := fun u => upDeriv ξ u t) MeasurableSet.univ
    (fun u _ => (hasDerivAt_upFlow hξ u ht).hasDerivWithinAt) (strictMono_upFlow hξ ht).injective.injOn g
  rw [image_univ, (surjective_upFlow hξ ht).range_eq, Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun u => ?_
  rw [abs_of_pos (upDeriv_pos u t)]

end InteractingSLE.ZhanGT4.Mix
