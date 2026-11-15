/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualD10Frozen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Capacity substitution including the seed entrance

Packet PROVE-ZHAN-GT4-A22. The monotone change of variables theorem has
no continuity assumption on the integrand. In particular, reciprocal seed
gaps may be unbounded at time zero. Integrability is transported as well
as the integral; the formula alone would not certify an entrance law.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE.ZhanGT4

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ}

/-- Capacity substitution for arbitrary real integrands, including seed
reciprocal gaps. No boundedness or continuity at the entrance is needed. -/
theorem OwnData.integral_capacity_substitution (h : OwnData W A φ T a W')
    (g : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∫ u in (0 : ℝ)..t, frzA W W' a φ 1 u ^ 2 * g (a u)) =
      ∫ v in (0 : ℝ)..a t, g v := by
  have hd (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) t) :
      HasDerivAt a (frzA W W' a φ 1 u ^ 2) u := by
    exact ((h.hasDerivWithinAt_clock ⟨hu.1.le, hu.2.le.trans ht.2⟩).1).hasDerivAt
      (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2))
  simpa only [uIcc_of_le ht.1, min_eq_left ht.1, max_eq_right ht.1,
    Function.comp_apply, smul_eq_mul, h.a0] using
    (intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
      (by simpa only [uIcc_of_le ht.1] using
        h.contA.mono (Icc_subset_Icc_right ht.2))
      (by simpa only [min_eq_left ht.1, max_eq_right ht.1] using hd) (fun u _ => sq_nonneg
        (frzA W W' a φ 1 u)) :
      (∫ u in (0 : ℝ)..t, frzA W W' a φ 1 u ^ 2 • (g ∘ a) u) =
        ∫ v in a 0..a t, g v)

/-- The capacity substitution also transports actual entrance
integrability. Thus it does not merely identify two possibly junk integrals. -/
theorem OwnData.intervalIntegrable_capacity_iff (h : OwnData W A φ T a W')
    (g : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun u => frzA W W' a φ 1 u ^ 2 * g (a u)) volume 0 t ↔
      IntervalIntegrable g volume 0 (a t) := by
  have hd (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) t) :
      HasDerivAt a (frzA W W' a φ 1 u ^ 2) u := by
    exact ((h.hasDerivWithinAt_clock ⟨hu.1.le, hu.2.le.trans ht.2⟩).1).hasDerivAt
      (Icc_mem_nhds hu.1 (hu.2.trans_le ht.2))
  simpa only [uIcc_of_le ht.1, min_eq_left ht.1, max_eq_right ht.1,
    Function.comp_apply, smul_eq_mul, h.a0] using
    (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
      (by simpa only [uIcc_of_le ht.1] using
        h.contA.mono (Icc_subset_Icc_right ht.2))
      (by simpa only [min_eq_left ht.1, max_eq_right ht.1] using hd) (fun u _ => sq_nonneg
        (frzA W W' a φ 1 u)) :
      IntervalIntegrable (fun u => frzA W W' a φ 1 u ^ 2 • (g ∘ a) u) volume 0 t ↔
        IntervalIntegrable g volume (a 0) (a t))

end InteractingSLE.ZhanGT4
