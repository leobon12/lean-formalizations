/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedClock
import InteractingSLE.Frozen.Spec.IsIntegratedSLEPath
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The time-changed two-seed construction solves the integrated equations

Packet PROVE-SEC2-JAC. The pathwise content of the two-seed existence step in the proof of
Theorem 2.2 (Specification pp. 23–24, `source/spec/p001-048.md` L522–L540): for a continuous path
`U : ℝ → [0, 1]` whose boundary set `{U ∈ {0, 1}}` is Lebesgue-null and whose clock
`t(u) = ½ ∫_{-∞}^u e^{2v} U_v (1 - U_v) dv` tends to `∞`, the processes

`V^L_t = L^-(u(t))`, `V^R_t = L^+(u(t))`, `W_t = w(u(t))` (`t > 0`), all `0` at `t = 0`,

together with `b_t = κ^{-1/2} (W_t + ½ ρ_L V^L_t + ½ ρ_R V^R_t)` (the source's formula for `B`,
Aux. lemma 4, L680) satisfy every pathwise condition of Definition 2.1 with force points at
`0⁻, 0⁺`, weights `ρ_L, ρ_R > -2` and infinite lifetime (`isIntegratedSLEPath_twoSeed`).

The source's reciprocal-gap identity
`∫_0^{t(u)} ds / (W_s - V^L_s) = ½ ∫_{-∞}^u e^v (1 - U_v) dv` (L536) is
`integral_inv_gapL`; it comes from the change of variables `s = t(v)`
(`integral_Ioc_clock_eq`), the clock being a strictly increasing `C¹` map of `ℝ` onto `(0, ∞)`.

That `b` is a Brownian motion (Itô's formula in the `u` clock, the inverse time change and Lévy's
characterization) is the stochastic half of the step and is not proved here.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

variable {U : ℝ → ℝ}

theorem phys_toNNReal (f : ℝ → ℝ) (s : ℝ) : phys U f (s.toNNReal : ℝ) = phys U f s := by
  rcases le_or_gt s 0 with hs | hs
  · rw [Real.toNNReal_of_nonpos hs, NNReal.coe_zero, phys_of_nonpos le_rfl, phys_of_nonpos hs]
  · rw [Real.coe_toNNReal _ hs.le]

section ChangeOfVariables

variable (hc : Continuous U) (h01 : ∀ v, U v ∈ Icc (0 : ℝ) 1)
  (hnull : volume {v | U v = 0 ∨ U v = 1} = 0) (htop : Tendsto (clock U) atTop atTop)
include hc h01 hnull htop

/-- The clock maps `(-∞, u]` onto `(0, t(u)]`. -/
theorem image_clock_Iic (u : ℝ) : clock U '' Iic u = Ioc 0 (clock U u) := by
  ext t
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨clock_pos hc h01 hnull v, monotone_clock hc h01 hv⟩
  · rintro ⟨ht0, htu⟩
    refine ⟨invClock U t, ?_, clock_invClock hc h01 htop ht0⟩
    exact not_lt.1 fun h => absurd htu (not_le.2 ((lt_invClock_iff hc h01 hnull htop ht0).1 h))

/-- Change of variables `s = t(v)`: `∫_{(0, t(u)]} g = ∫_{(-∞, u]} t'(v) g(t(v)) dv`. -/
theorem integral_Ioc_clock_eq (g : ℝ → ℝ) (u : ℝ) :
    ∫ s in Ioc 0 (clock U u), g s = ∫ v in Iic u, clockDensity U v * g (clock U v) := by
  rw [← image_clock_Iic hc h01 hnull htop, integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
    (fun v _ => (hasDerivAt_clock hc h01 v).hasDerivWithinAt)
    (strictMono_clock hc h01 hnull).injective.injOn g]
  refine setIntegral_congr_fun measurableSet_Iic fun v _ => ?_
  rw [abs_of_nonneg (clockDensity_nonneg h01 v), smul_eq_mul]

theorem integrableOn_Ioc_clock_iff (g : ℝ → ℝ) (u : ℝ) :
    IntegrableOn g (Ioc 0 (clock U u)) ↔
      IntegrableOn (fun v => clockDensity U v * g (clock U v)) (Iic u) := by
  rw [← image_clock_Iic hc h01 hnull htop, integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Iic (fun v _ => (hasDerivAt_clock hc h01 v).hasDerivWithinAt)
    (strictMono_clock hc h01 hnull).injective.injOn g]
  refine integrableOn_congr_fun (fun v _ => ?_) measurableSet_Iic
  simp only [abs_of_nonneg (clockDensity_nonneg h01 v), smul_eq_mul]

omit hc h01 htop in
/-- Almost every `v` has `U v ∉ {0, 1}`. -/
theorem ae_ne_zero_ne_one : ∀ᵐ v ∂volume, U v ≠ 0 ∧ U v ≠ 1 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with v hv
  simp only [not_or] at hv
  exact hv

/-- The physical left gap at `s = t(v)` is `e^v U_v`. -/
theorem phys_driver_sub_phys_lowerL_clock (v : ℝ) :
    phys U (driver U) (clock U v) - phys U (lowerL U) (clock U v) = exp v * U v := by
  rw [phys_of_pos (clock_pos hc h01 hnull v), phys_of_pos (clock_pos hc h01 hnull v),
    invClock_clock hc h01 hnull htop, driver_sub_lowerL]

/-- The physical right gap at `s = t(v)` is `e^v (1 - U_v)`. -/
theorem phys_upperL_sub_phys_driver_clock (v : ℝ) :
    phys U (upperL U) (clock U v) - phys U (driver U) (clock U v) = exp v * (1 - U v) := by
  rw [phys_of_pos (clock_pos hc h01 hnull v), phys_of_pos (clock_pos hc h01 hnull v),
    invClock_clock hc h01 hnull htop, upperL_sub_driver hc h01]

/-- `t'(v) / (e^v U_v) = ½ e^v (1 - U_v)` almost everywhere. -/
theorem clockDensity_mul_inv_gapL_ae :
    (fun v => clockDensity U v *
        (phys U (driver U) (clock U v) - phys U (lowerL U) (clock U v))⁻¹) =ᵐ[volume]
      fun v => exp v * (1 - U v) / 2 := by
  filter_upwards [ae_ne_zero_ne_one hnull] with v hv
  rw [phys_driver_sub_phys_lowerL_clock hc h01 hnull htop, clockDensity]
  have := (exp_pos v).ne'
  field_simp [hv.1]
  rw [show exp (2 * v) = exp v * exp v by rw [← exp_add]; ring_nf]
  ring

/-- `t'(v) / (e^v (1 - U_v)) = ½ e^v U_v` almost everywhere. -/
theorem clockDensity_mul_inv_gapR_ae :
    (fun v => clockDensity U v *
        (phys U (upperL U) (clock U v) - phys U (driver U) (clock U v))⁻¹) =ᵐ[volume]
      fun v => exp v * U v / 2 := by
  filter_upwards [ae_ne_zero_ne_one hnull] with v hv
  rw [phys_upperL_sub_phys_driver_clock hc h01 hnull htop, clockDensity]
  have := (exp_pos v).ne'
  have h1 : 1 - U v ≠ 0 := sub_ne_zero.2 (Ne.symm hv.2)
  field_simp [h1]
  rw [show exp (2 * v) = exp v * exp v by rw [← exp_add]; ring_nf]
  ring

/-- Integrability of the left reciprocal gap on `(0, T]`. -/
theorem integrableOn_inv_gapL (T : ℝ) :
    IntegrableOn (fun s => (phys U (driver U) s - phys U (lowerL U) s)⁻¹) (Ioc 0 T) := by
  rcases le_or_gt T 0 with hT | hT
  · rw [Ioc_eq_empty (not_lt.2 hT)]; exact integrableOn_empty
  rw [← clock_invClock hc h01 htop hT, integrableOn_Ioc_clock_iff hc h01 hnull htop]
  refine IntegrableOn.congr_fun_ae ?_
    (ae_restrict_of_ae (clockDensity_mul_inv_gapL_ae hc h01 hnull htop).symm)
  exact (integrableOn_exp_mul_one_sub hc h01 _).div_const 2

/-- Integrability of the right reciprocal gap on `(0, T]`. -/
theorem integrableOn_inv_gapR (T : ℝ) :
    IntegrableOn (fun s => (phys U (upperL U) s - phys U (driver U) s)⁻¹) (Ioc 0 T) := by
  rcases le_or_gt T 0 with hT | hT
  · rw [Ioc_eq_empty (not_lt.2 hT)]; exact integrableOn_empty
  rw [← clock_invClock hc h01 htop hT, integrableOn_Ioc_clock_iff hc h01 hnull htop]
  refine IntegrableOn.congr_fun_ae ?_
    (ae_restrict_of_ae (clockDensity_mul_inv_gapR_ae hc h01 hnull htop).symm)
  exact (integrableOn_exp_mul hc h01 _).div_const 2

/-- **The left reciprocal-gap integral** (Specification p. 23, L536):
`∫_0^T ds / (W_s - V^L_s) = -½ V^L_T`, i.e. `½ ∫_{-∞}^{u(T)} e^v (1 - U_v) dv`. -/
theorem integral_inv_gapL (T : ℝ) :
    ∫ s in Ioc 0 T, (phys U (driver U) s - phys U (lowerL U) s)⁻¹ = -phys U (lowerL U) T / 2 := by
  rcases le_or_gt T 0 with hT | hT
  · rw [Ioc_eq_empty (not_lt.2 hT), setIntegral_empty, phys_of_nonpos hT]; ring
  conv_lhs => rw [← clock_invClock hc h01 htop hT]
  rw [integral_Ioc_clock_eq hc h01 hnull htop,
    setIntegral_congr_ae measurableSet_Iic ((clockDensity_mul_inv_gapL_ae hc h01 hnull htop).mono
      fun v hv _ => hv), integral_div, phys_of_pos hT, lowerL]
  ring

/-- **The right reciprocal-gap integral**: `∫_0^T ds / (V^R_s - W_s) = ½ V^R_T`. -/
theorem integral_inv_gapR (T : ℝ) :
    ∫ s in Ioc 0 T, (phys U (upperL U) s - phys U (driver U) s)⁻¹ = phys U (upperL U) T / 2 := by
  rcases le_or_gt T 0 with hT | hT
  · rw [Ioc_eq_empty (not_lt.2 hT), setIntegral_empty, phys_of_nonpos hT]; ring
  conv_lhs => rw [← clock_invClock hc h01 htop hT]
  rw [integral_Ioc_clock_eq hc h01 hnull htop,
    setIntegral_congr_ae measurableSet_Iic ((clockDensity_mul_inv_gapR_ae hc h01 hnull htop).mono
      fun v hv _ => hv), integral_div, phys_of_pos hT, upperL]

/-- `∫_0^T ρ / (W_s - V^L_s) ds = -½ ρ V^L_T`. -/
theorem integral_driftL (ρ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in (0 : ℝ)..T, ρ / (phys U (driver U) s - phys U (lowerL U) s) =
      -(ρ * phys U (lowerL U) T) / 2 := by
  rw [intervalIntegral.integral_of_le hT]
  simp only [div_eq_mul_inv ρ]
  rw [integral_const_mul, integral_inv_gapL hc h01 hnull htop]
  ring

/-- `∫_0^T ρ / (W_s - V^R_s) ds = -½ ρ V^R_T`. -/
theorem integral_driftR (ρ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in (0 : ℝ)..T, ρ / (phys U (driver U) s - phys U (upperL U) s) =
      -(ρ * phys U (upperL U) T) / 2 := by
  rw [intervalIntegral.integral_of_le hT]
  have : ∀ s, ρ / (phys U (driver U) s - phys U (upperL U) s) =
      -ρ * (phys U (upperL U) s - phys U (driver U) s)⁻¹ := fun s => by
    rw [← neg_sub, div_neg, div_eq_mul_inv]; ring
  simp only [this]
  rw [integral_const_mul, integral_inv_gapR hc h01 hnull htop]
  ring

/-- `∫_0^T 2 / (V^L_s - W_s) ds = V^L_T`. -/
theorem integral_forceL {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in (0 : ℝ)..T, 2 / (phys U (lowerL U) s - phys U (driver U) s) = phys U (lowerL U) T := by
  rw [intervalIntegral.integral_of_le hT]
  have : ∀ s, 2 / (phys U (lowerL U) s - phys U (driver U) s) =
      -2 * (phys U (driver U) s - phys U (lowerL U) s)⁻¹ := fun s => by
    rw [← neg_sub, div_neg, div_eq_mul_inv]; ring
  simp only [this]
  rw [integral_const_mul, integral_inv_gapL hc h01 hnull htop]
  ring

/-- `∫_0^T 2 / (V^R_s - W_s) ds = V^R_T`. -/
theorem integral_forceR {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in (0 : ℝ)..T, 2 / (phys U (upperL U) s - phys U (driver U) s) = phys U (upperL U) T := by
  rw [intervalIntegral.integral_of_le hT]
  simp only [div_eq_mul_inv (2 : ℝ)]
  rw [integral_const_mul, integral_inv_gapR hc h01 hnull htop]
  ring

omit hc hnull htop in
theorem phys_lowerL_le_phys_driver (x : ℝ) : phys U (lowerL U) x ≤ phys U (driver U) x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [phys_of_nonpos hx, phys_of_nonpos hx]
  · rw [phys_of_pos hx, phys_of_pos hx]; exact lowerL_le_driver h01 _

omit hnull htop in
theorem phys_driver_le_phys_upperL (x : ℝ) : phys U (driver U) x ≤ phys U (upperL U) x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [phys_of_nonpos hx, phys_of_nonpos hx]
  · rw [phys_of_pos hx, phys_of_pos hx]; exact driver_le_upperL hc h01 _

/-- The physical collision set with the left force point is contained in `{0} ∪ t({U = 0})`, a
null set. -/
theorem volume_collisionL :
    volume {s : ℝ | 0 ≤ s ∧ phys U (driver U) s = phys U (lowerL U) s} = 0 := by
  have hsub : {s : ℝ | 0 ≤ s ∧ phys U (driver U) s = phys U (lowerL U) s} ⊆
      {0} ∪ clock U '' {v | U v = 0 ∨ U v = 1} := by
    rintro s ⟨hs0, hs⟩
    rcases hs0.eq_or_lt with rfl | hs0
    · exact Or.inl rfl
    refine Or.inr ⟨invClock U s, Or.inl ?_, ?_⟩
    · rw [phys_of_pos hs0, phys_of_pos hs0, ← sub_eq_zero, driver_sub_lowerL] at hs
      exact (mul_eq_zero.1 hs).resolve_left (exp_pos _).ne'
    · exact clock_invClock hc h01 htop hs0
  refine measure_mono_null hsub (measure_union_null (by simp) ?_)
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (fun v _ => (hasDerivAt_clock hc h01 v).differentiableAt.differentiableWithinAt) hnull

/-- The physical collision set with the right force point is null. -/
theorem volume_collisionR :
    volume {s : ℝ | 0 ≤ s ∧ phys U (driver U) s = phys U (upperL U) s} = 0 := by
  have hsub : {s : ℝ | 0 ≤ s ∧ phys U (driver U) s = phys U (upperL U) s} ⊆
      {0} ∪ clock U '' {v | U v = 0 ∨ U v = 1} := by
    rintro s ⟨hs0, hs⟩
    rcases hs0.eq_or_lt with rfl | hs0
    · exact Or.inl rfl
    refine Or.inr ⟨invClock U s, Or.inr ?_, ?_⟩
    · rw [phys_of_pos hs0, phys_of_pos hs0, eq_comm, ← sub_eq_zero, upperL_sub_driver hc h01] at hs
      have := (mul_eq_zero.1 hs).resolve_left (exp_pos _).ne'
      linarith
    · exact clock_invClock hc h01 htop hs0
  refine measure_mono_null hsub (measure_union_null (by simp) ?_)
  exact addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (fun v _ => (hasDerivAt_clock hc h01 v).differentiableAt.differentiableWithinAt) hnull

end ChangeOfVariables

/-! ### The two-seed paths in the form of Definition 2.1 -/

/-- The driving path `W` of the two-seed construction, on `ℝ≥0`. -/
def wPath (U : ℝ → ℝ) (t : ℝ≥0) : ℝ := phys U (driver U) t

/-- The left force path `V^L` (one left force point, started at `0⁻`). -/
def vLPath (U : ℝ → ℝ) (_ : Fin 1) (t : ℝ≥0) : ℝ := phys U (lowerL U) t

/-- The right force path `V^R` (one right force point, started at `0⁺`). -/
def vRPath (U : ℝ → ℝ) (_ : Fin 1) (t : ℝ≥0) : ℝ := phys U (upperL U) t

/-- The driving Brownian path determined by the integrated driving equation (Specification p. 29,
L680): `b_t = κ^{-1/2} (W_t + ½ ρ_L V^L_t + ½ ρ_R V^R_t)`. -/
def bPath (κ : ℝ) (ρL ρR : Fin 1 → ℝ) (U : ℝ → ℝ) (t : ℝ≥0) : ℝ :=
  (wPath U t + ρL 0 / 2 * phys U (lowerL U) t + ρR 0 / 2 * phys U (upperL U) t) / Real.sqrt κ

/-- With one force point per side and weights `> -2`, the threshold condition never holds. -/
theorem sum_filter_fin_one_gt {ρ : Fin 1 → ℝ} (hρ : ∀ i, -2 < ρ i) (p : Fin 1 → Prop)
    [DecidablePred p] : -2 < ∑ i ∈ Finset.univ.filter p, ρ i := by
  rw [Finset.sum_filter, Fin.sum_univ_one]
  split_ifs
  · exact hρ 0
  · norm_num

theorem not_thresholdCondition_fin_one {ρL ρR : Fin 1 → ℝ} (hρL : ∀ i, -2 < ρL i)
    (hρR : ∀ i, -2 < ρR i) (w : ℝ) (vL vR : Fin 1 → ℝ) :
    ¬ ForceWord.ThresholdCondition ρL ρR w vL vR := by
  rintro (h | h)
  · exact absurd h (not_le.2 (sum_filter_fin_one_gt hρL _))
  · exact absurd h (not_le.2 (sum_filter_fin_one_gt hρR _))

/-- **The time-changed two-seed construction satisfies Definition 2.1** (Specification p. 23–24,
L522–L540, "this construction satisfies all three conditions of Definition 2.1"), pathwise: for a
continuous `U : ℝ → [0, 1]` with Lebesgue-null boundary set and divergent clock, the paths
`W = w ∘ u`, `V^L = L^- ∘ u`, `V^R = L^+ ∘ u` with `b = κ^{-1/2}(W + ½ρ_L V^L + ½ρ_R V^R)` satisfy
`IsIntegratedSLEPath` for the force word `(0⁻; 0⁺)` with weights `ρ_L, ρ_R > -2` and lifetime `∞`. -/
theorem isIntegratedSLEPath_twoSeed (hc : Continuous U) (h01 : ∀ v, U v ∈ Icc (0 : ℝ) 1)
    (hnull : volume {v | U v = 0 ∨ U v = 1} = 0) (htop : Tendsto (clock U) atTop atTop)
    {κ : ℝ} (hκ : 0 < κ) {ρL ρR : Fin 1 → ℝ} (hρL : ∀ i, -2 < ρL i) (hρR : ∀ i, -2 < ρR i) :
    IsIntegratedSLEPath κ (fun _ => 0) (fun _ => 0) ρL ρR (wPath U) (vLPath U) (vRPath U)
      (bPath κ ρL ρR U) ⊤ := by
  have hw0 : ∀ f : ℝ → ℝ, phys U f ((0 : ℝ≥0) : ℝ) = 0 := fun f => phys_of_nonpos le_rfl
  have hcont : ∀ f : ℝ → ℝ, Continuous f → Tendsto f atBot (𝓝 0) →
      ContinuousOn (fun t : ℝ≥0 => phys U f t) {t | (t : ℝ≥0∞) < ⊤} := fun f hf hf0 =>
    ((continuous_phys hc h01 hnull htop hf hf0).comp NNReal.continuous_coe).continuousOn
  have hW : ∀ s : ℝ, wPath U s.toNNReal = phys U (driver U) s := fun s => phys_toNNReal _ s
  have hL : ∀ i s, vLPath U i s.toNNReal = phys U (lowerL U) s := fun _ s => phys_toNNReal _ s
  have hR : ∀ i s, vRPath U i s.toNNReal = phys U (upperL U) s := fun _ s => phys_toNNReal _ s
  have hsq : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  refine ⟨hw0 _, fun _ => hw0 _, fun _ => hw0 _, hcont _ (continuous_driver hc h01)
    (tendsto_driver_atBot hc h01), fun _ => hcont _ (continuous_lowerL hc h01)
    (tendsto_lowerL_atBot hc h01), fun _ => hcont _ (continuous_upperL hc h01)
    (tendsto_upperL_atBot hc h01), fun _ _ _ _ _ => le_rfl,
    fun t _ _ => phys_lowerL_le_phys_driver h01 _, fun t _ _ => phys_driver_le_phys_upperL hc h01 _,
    fun _ _ _ _ _ => le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- integrable_gapL
    intro t _ i
    simp only [hW, hL]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg t)).2
      (integrableOn_inv_gapL hc h01 hnull htop t)
  · -- integrable_gapR
    intro t _ i
    simp only [hW, hR]
    have : (fun s => (phys U (driver U) s - phys U (upperL U) s)⁻¹) =
        fun s => -(phys U (upperL U) s - phys U (driver U) s)⁻¹ := by
      funext s; rw [← neg_sub, inv_neg]
    rw [this]
    exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg t)).2
      (integrableOn_inv_gapR hc h01 hnull htop t)).neg
  · -- w_eq
    intro t _
    simp only [hW, hL, hR, Fin.sum_univ_one]
    rw [integral_driftL hc h01 hnull htop _ (NNReal.coe_nonneg t),
      integral_driftR hc h01 hnull htop _ (NNReal.coe_nonneg t), bPath,
      mul_div_cancel₀ _ hsq, wPath]
    ring
  · -- vL_eq
    intro t _ i
    simp only [hW, hL]
    rw [integral_forceL hc h01 hnull htop (NNReal.coe_nonneg t), zero_add, vLPath]
  · -- vR_eq
    intro t _ i
    simp only [hW, hR]
    rw [integral_forceR hc h01 hnull htop (NNReal.coe_nonneg t), zero_add, vRPath]
  · -- volume_collisionL
    intro i
    simp only [hW, hL, ENNReal.coe_lt_top, true_and]
    exact volume_collisionL hc h01 hnull htop
  · -- volume_collisionR
    intro i
    simp only [hW, hR, ENNReal.coe_lt_top, true_and]
    exact volume_collisionR hc h01 hnull htop
  · -- not_threshold
    intro t _
    exact not_thresholdCondition_fin_one hρL hρR _ _ _
  · -- threshold_of_eq_zero
    intro h
    exact absurd h ENNReal.top_ne_zero
  · -- threshold_of_tendsto
    intro T _ hT
    exact absurd hT ENNReal.coe_ne_top

end TwoSeed

end Sec2

end InteractingSLE
