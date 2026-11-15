/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowLocalityGenKernelProb
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Discounted lifetimes and strict conditional gaps

The discount is strictly decreasing on the extended time line, including at
infinity. Strict conditional positivity is reused from the locality API.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

/-- A bounded strictly decreasing lifetime observable, equal to zero at infinity. -/
def survivalDiscount (v : ℝ≥0∞) : ℝ := ((v + 1)⁻¹).toReal

/-- The lifetime discount is Borel. -/
theorem measurable_survivalDiscount : Measurable survivalDiscount :=
  ENNReal.measurable_toReal.comp ((measurable_id.add_const 1).inv)

/-- The discount of a finite time is the ordinary reciprocal of time plus one. -/
theorem survivalDiscount_coe (t : ℝ≥0) : survivalDiscount (t : ℝ≥0∞) = ((t : ℝ) + 1)⁻¹ := by
  simp [survivalDiscount, ENNReal.toReal_add]

/-- The discount vanishes at infinity. -/
theorem survivalDiscount_top : survivalDiscount ⊤ = 0 := by
  simp [survivalDiscount]

/-- The discount has values in the unit interval. -/
theorem survivalDiscount_mem_Icc (v : ℝ≥0∞) : survivalDiscount v ∈ Icc (0 : ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have h : (v + 1)⁻¹ ≤ (1 : ℝ≥0∞) := ENNReal.inv_le_one.2 (le_add_left le_rfl)
  simpa only [survivalDiscount, ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top h

/-- Strict decrease holds also when the larger lifetime is infinite. -/
theorem strictAnti_survivalDiscount : StrictAnti survivalDiscount := by
  intro a b hab
  have hn (v : ℝ≥0∞) : (v + 1)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 (by simp)
  exact (ENNReal.toReal_lt_toReal (hn b) (hn a)).2
    (ENNReal.inv_strictAnti ((ENNReal.add_lt_add_iff_right ENNReal.one_ne_top).2 hab))

/-- Bounded measurable lifetime discounts are integrable under a finite measure. -/
theorem integrable_survivalDiscount {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {V : Ω → ℝ≥0∞} (hV : Measurable V) :
    Integrable (fun ω => survivalDiscount (V ω)) P :=
  Integrable.of_bound (measurable_survivalDiscount.comp hV).aestronglyMeasurable 1
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (survivalDiscount_mem_Icc (V ω)).1]
      exact (survivalDiscount_mem_Icc (V ω)).2)

/-- On an observed event where an integrable variable is strictly below an
observed bound, its conditional expectation is strictly below that bound.
This is an indicator adapter to the existing strict-positivity theorem. -/
theorem ae_condExp_lt_on_event {Ω : Type*} {m mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] (hm : m ≤ mΩ)
    {A : Set Ω} (hA : MeasurableSet[m] A) {f g : Ω → ℝ}
    (hf : Integrable f P) (hg : Integrable g P) (hgm : StronglyMeasurable[m] g)
    (hlt : ∀ ω ∈ A, f ω < g ω) :
    ∀ᵐ ω ∂P, ω ∈ A → P[f | m] ω < g ω := by
  let Z : Ω → ℝ := A.indicator (g - f) + Aᶜ.indicator (fun _ => 1)
  have hZi : Integrable Z P :=
    ((hg.sub hf).indicator (hm _ hA)).add ((integrable_const 1).indicator (hm _ hA.compl))
  have hZpos : ∀ ω, 0 < Z ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simpa [Z, hω, Pi.sub_apply] using sub_pos.2 (hlt ω hω)
    · simp [Z, hω]
  have he := condExp_add ((hg.sub hf).indicator (hm _ hA))
    ((integrable_const (1 : ℝ)).indicator (hm _ hA.compl)) m
  filter_upwards [Restart.FlowLocalityGen.ae_condExp_pos_of_pos hm hZi hZpos, he,
    condExp_indicator (hg.sub hf) hA, condExp_indicator (integrable_const (1 : ℝ)) hA.compl,
    condExp_sub hg hf m] with ω hpos he hi hc hs hω
  have hge : P[g | m] ω = g ω := congrFun (condExp_of_stronglyMeasurable hm hgm hg) ω
  simp only [Pi.add_apply] at he
  rw [he, hi, hc, indicator_of_mem hω, indicator_of_notMem (notMem_compl_iff.2 hω),
    add_zero, hs, Pi.sub_apply, hge] at hpos
  exact sub_pos.1 hpos

end InteractingSLE.WFS
