/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1BorelTime

/-!
# A closed algebraic test for equality of retargeted tips

Continuation of PROVE-GW1-DET. In trace coordinates the translated inversion
tip relation is `a * (1 + v * b) = b`. This identity includes the zero case,
where neither chart has a finite tip, and is stable under limits in time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal NNRat

namespace InteractingSLE.Theorem14.GW1Borel

theorem inversion_tip_iff (a b v : ℂ) :
    (∀ z : ℂ, (a ≠ 0 ∧ z = v - a⁻¹) ↔ (b ≠ 0 ∧ z = -b⁻¹)) ↔
      a * (1 + v * b) = b := by
  by_cases ha : a = 0
  · subst a
    simp only [ne_eq, not_true_eq_false, false_and, false_iff, zero_mul]
    constructor
    · intro h
      by_contra hb
      exact h (-b⁻¹) ⟨Ne.symm hb, rfl⟩
    · rintro rfl z
      exact fun h => h.1 rfl
  by_cases hb : b = 0
  · subst b
    simp only [ne_eq, not_true_eq_false, false_and, iff_false, mul_zero, add_zero, mul_one]
    constructor
    · intro h
      exact False.elim (h (v - a⁻¹) ⟨ha, rfl⟩)
    · intro h
      exact False.elim (ha h)
  have hpoint : (∀ z : ℂ, (a ≠ 0 ∧ z = v - a⁻¹) ↔ (b ≠ 0 ∧ z = -b⁻¹)) ↔
      v - a⁻¹ = -b⁻¹ := by
    constructor
    · intro h
      exact ((h (v - a⁻¹)).1 ⟨ha, rfl⟩).2
    · intro h z
      constructor
      · rintro ⟨_, rfl⟩
        exact ⟨hb, h⟩
      · rintro ⟨_, rfl⟩
        exact ⟨ha, h.symm⟩
  rw [hpoint]
  field_simp
  constructor <;> intro h <;> linear_combination h

/-- The original finite-tip equivalence is precisely the polynomial trace identity. -/
theorem tipAt_iff_polynomial (U Q : RegularCode) (v : ℝ) (r s : ℝ≥0) :
    (∀ z : ℂ, ((Chart.id.recenter v).trans infinitySourceChart).tipAt (driver U.1) r z ↔
      infinitySourceChart.tipAt (driver Q.1) s z) ↔
      trace U r * (1 + (v : ℂ) * trace Q s) = trace Q s := by
  have h := inversion_tip_iff (trace U r) (trace Q s) (v : ℂ)
  convert h using 3
  · rw [GW1Det.tipAt_recenter_infinity_iff,
      GW4Leaf.tipAt_infinitySourceChart_iff (trace_properties U).1 (continuous_driver _) (driver_zero _)]
    constructor <;> rintro ⟨hne, hz⟩ <;> refine ⟨hne, ?_⟩ <;> linear_combination hz
  · exact GW4Leaf.tipAt_infinitySourceChart_iff (trace_properties Q).1
      (continuous_driver _) (driver_zero _) _ _

/-- A continuous trace identity is determined by its rational-time values. -/
theorem polynomial_iff_rat (U Q : RegularCode) (v : ℝ) {ℓ : ℝ≥0 → ℝ≥0} (hℓ : Continuous ℓ) :
    (∀ r : ℝ≥0, trace U r * (1 + (v : ℂ) * trace Q (ℓ r)) = trace Q (ℓ r)) ↔
      ∀ q : ℚ≥0, trace U q * (1 + (v : ℂ) * trace Q (ℓ q)) = trace Q (ℓ q) := by
  refine ⟨fun h q => h q, fun h r => ?_⟩
  have hQc := (continuous_trace Q).comp hℓ
  have hc : Continuous (fun t => trace U t * (1 + (v : ℂ) * trace Q (ℓ t))) :=
    (continuous_trace U).mul (continuous_const.add (continuous_const.mul hQc))
  exact tendsto_nhds_unique
    ((hc.tendsto r).comp (Sec7.Coding.tendsto_apxQ r))
    (((hQc.tendsto r).comp (Sec7.Coding.tendsto_apxQ r)).congr'
      (Eventually.of_forall fun n => (h (Sec7.Coding.apxQ r n)).symm))

end InteractingSLE.Theorem14.GW1Borel
