/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# Bounded representatives of real L¹ functionals

We obtain L¹ duality on a probability space by restricting to L², applying
Fréchet--Riesz, testing indicators, and using the density of simple functions.
This is the functional-analytic ingredient of Douglas separation.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.WFS

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- The probability-space inclusion L² → L¹. -/
def l2ToL1 : Lp ℝ 2 P →L[ℝ] Lp ℝ 1 P :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨f.1,
        ((Lp.memLp f).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun f => by
      change (eLpNorm f 1 P).toReal ≤ 1 * (eLpNorm f 2 P).toReal
      rw [one_mul]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable f)))

theorem coeFn_l2ToL1 (f : Lp ℝ 2 P) : l2ToL1 P f =ᵐ[P] f :=
  Filter.EventuallyEq.rfl

/-- The L² representative of a real L¹ functional, with its sharp a.e. bound. -/
theorem exists_bounded_l2_representative (L : Lp ℝ 1 P →L[ℝ] ℝ) :
    ∃ h : Lp ℝ 2 P, (∀ f : Lp ℝ 2 P,
      (∫ x, h x * f x ∂P) = L (l2ToL1 P f)) ∧ ∀ᵐ x ∂P, ‖h x‖ ≤ ‖L‖ := by
  let h := (InnerProductSpace.toDual ℝ (Lp ℝ 2 P)).symm (L.comp (l2ToL1 P))
  have hr (f : Lp ℝ 2 P) : (∫ x, h x * f x ∂P) = L (l2ToL1 P f) := by
    simpa only [L2.inner_def, RCLike.inner_apply, conj_trivial, mul_comm,
      ContinuousLinearMap.comp_apply] using
      (InnerProductSpace.toDual_symm_apply (x := f) (y := L.comp (l2ToL1 P)))
  have hi : Integrable h P :=
    memLp_one_iff_integrable.1 ((Lp.memLp h).mono_exponent (by norm_num))
  have hs (s : Set Ω) (hsm : MeasurableSet s) :
      (∫ x in s, h x ∂P) = L (indicatorConstLp 1 hsm (measure_ne_top P s) (1 : ℝ)) := by
    let f := indicatorConstLp 2 hsm (measure_ne_top P s) (1 : ℝ)
    have hfl : l2ToL1 P f = indicatorConstLp 1 hsm (measure_ne_top P s) (1 : ℝ) := by
      apply Lp.ext
      exact (coeFn_l2ToL1 P f).trans
        (indicatorConstLp_coeFn.trans indicatorConstLp_coeFn.symm)
    rw [← hfl, ← hr f, ← integral_indicator hsm]
    apply integral_congr_ae
    filter_upwards [@indicatorConstLp_coeFn Ω ℝ _ 2 P _ s hsm
      (measure_ne_top P s) (1 : ℝ)] with x hx
    dsimp only [f]
    rw [hx]
    by_cases hxs : x ∈ s <;> simp only [Set.indicator_of_mem, Set.indicator_of_notMem, hxs,
      mul_one, mul_zero, not_false_eq_true]
  have hb (s : Set Ω) (hsm : MeasurableSet s) :
      ‖∫ x in s, h x ∂P‖ ≤ ‖L‖ * P.real s := by
    rw [hs s hsm]
    simpa only [norm_indicatorConstLp one_ne_zero ENNReal.one_ne_top, norm_one, ENNReal.toReal_one,
      div_one, Real.rpow_one, one_mul] using
      L.le_opNorm (indicatorConstLp 1 hsm (measure_ne_top P s) (1 : ℝ))
  have hu : h ≤ᵐ[P] fun _ => ‖L‖ := by
    apply ae_le_of_forall_setIntegral_le hi (integrable_const ‖L‖)
    intro s hsm _
    rw [setIntegral_const, smul_eq_mul, mul_comm]
    exact (le_abs_self _).trans (hb s hsm)
  have hl : (fun _ => -‖L‖) ≤ᵐ[P] h := by
    apply ae_le_of_forall_setIntegral_le (integrable_const (-‖L‖)) hi
    intro s hsm _
    rw [setIntegral_const, smul_eq_mul]
    have := neg_le_of_abs_le (by simpa only [Real.norm_eq_abs] using hb s hsm)
    nlinarith only [this]
  refine ⟨h, hr, ?_⟩
  filter_upwards [hu, hl] with x hx hy
  exact (abs_le.2 ⟨hy, hx⟩ : |h x| ≤ ‖L‖)

end InteractingSLE.WFS
