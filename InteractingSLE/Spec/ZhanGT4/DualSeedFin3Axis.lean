/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Height

/-!
# Identity-chart normalization of the concrete seeded field

Packet PROVE-ZHAN-GT4-A22. Divided differences retain their derivative
values at coincident seeds. The identity-chart calculation therefore
normalizes both axes, with no seed noncollision assumption at time zero.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4
namespace SeedData

/-- The actual normalized log density vanishes in an identity chart,
including coincident force coordinates. The listed identities are exactly
the map and derivative factors of that chart. -/
theorem normEll_eq_zero_of_identity {n : ℕ} (d : SeedData n) (t : ℝ)
    (hf : d.F 0 t = id) (hA : d.A 1 t = 1) (h21 : d.A21 t = 1)
    (hB : ∀ m, d.B1 t m = 1) (h20 : d.A20 t = d.V₀ t) (hL : d.L t = 0) :
    d.normEll t = 0 := by
  have h0 : d.A 0 t = d.W t := by
    rw [← d.F_driver 0 t, hf]
    rfl
  have hB0 (m : Fin n) : d.B0 t m = d.V m t := by
    change d.F 0 t (d.V m t) = _
    rw [hf]
    rfl
  have hds (x y : ℝ) : dslope (id : ℝ → ℝ) x y = 1 := by
    by_cases hxy : y = x
    · subst y
      rw [dslope_same]
      exact deriv_id x
    · rw [dslope_of_ne _ hxy, slope_def_field]
      exact div_self (sub_ne_zero.2 hxy)
  simp only [normEll, hA, h21, hB, h20, hL, h0, hB0, hf, hds,
    Real.log_one, Real.log_div_self, mul_zero, zero_sub, neg_zero,
    add_zero, Finset.sum_const_zero, pairSum]

end SeedData

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Both axes of the concrete two-time field are one when the zero-height
records have the identity-chart factors. No initial seed gap is required. -/
theorem seedHeightField_axes_of_identity {n : ℕ} {d : ℝ → Ω → SeedData n}
    (hf : ∀ ω t, (d 0 ω).F 0 t = id) (hA : ∀ ω t, (d 0 ω).A 1 t = 1)
    (h21 : ∀ ω t, (d 0 ω).A21 t = 1) (hB : ∀ ω t m, (d 0 ω).B1 t m = 1)
    (h20 : ∀ ω t, (d 0 ω).A20 t = (d 0 ω).V₀ t) (hL : ∀ ω t, (d 0 ω).L t = 0) :
    (∀ ω t, seedHeightField d ω 0 t = 1) ∧ (∀ ω s, seedHeightField d ω s 0 = 1) := by
  refine ⟨seedHeightField_zero_left d, seedHeightField_zero_right ?_⟩
  intro ω s
  rw [(d 0 ω).normEll_eq_zero_of_identity s (hf ω s) (hA ω s) (h21 ω s) (hB ω s) (h20 ω s) (hL ω s),
    (d 0 ω).normEll_eq_zero_of_identity 0 (hf ω 0) (hA ω 0) (h21 ω 0) (hB ω 0) (h20 ω 0) (hL ω 0)]

end InteractingSLE.ZhanGT4
