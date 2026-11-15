/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedCloseClock
import InteractingSLE.Spec.ZhanGT4.DualSeedImageMarks

/-!
# Integrated seed force equations in capacity time

Packet PROVE-ZHAN-GT4-A22. Transport both the entrance integrability and
the actual integrated force equation. The spatial translation is common
to the driver and forces, and need not vanish at time zero.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE.ZhanGT4

/-- An own-time force equation becomes the capacity force equation even
when its initial gap vanishes. The hypotheses on `w` and `v` merely specify
the coordinates under the actual capacity clock. -/
theorem OwnData.capacity_force_equation
    {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ}
    (h : OwnData W A φ T a W') {V w v : ℝ → ℝ} {c t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T)
    (hw : ∀ u ∈ Icc (0 : ℝ) T, w (a u) = frzA W W' a φ 0 u - c)
    (hv : ∀ u ∈ Icc (0 : ℝ) T, v (a u) = V u - c)
    (hi : IntervalIntegrable (fun u => 2 * frzA W W' a φ 1 u ^ 2 /
      (V u - frzA W W' a φ 0 u)) volume 0 t)
    (he : V t = V 0 + ∫ u in (0 : ℝ)..t,
      2 * frzA W W' a φ 1 u ^ 2 / (V u - frzA W W' a φ 0 u)) :
    IntervalIntegrable (fun u => (w u - v u)⁻¹) volume 0 (a t) ∧
      v (a t) = v 0 + ∫ u in (0 : ℝ)..a t, 2 / (v u - w u) := by
  have hm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) t) : u ∈ Icc (0 : ℝ) T :=
    ⟨hu.1, hu.2.trans ht.2⟩
  have hi' : IntervalIntegrable
      (fun u => frzA W W' a φ 1 u ^ 2 * (w (a u) - v (a u))⁻¹) volume 0 t := by
    apply (hi.const_mul (-(1 / 2) : ℝ)).congr
    intro u hu
    rw [uIoc_of_le ht.1] at hu
    dsimp only
    rw [hw u (hm u ⟨hu.1.le, hu.2⟩), hv u (hm u ⟨hu.1.le, hu.2⟩)]
    rw [sub_sub_sub_cancel_right]
    rw [show V u - frzA W W' a φ 0 u = -(frzA W W' a φ 0 u - V u) by ring,
      div_neg, inv_eq_one_div]
    ring
  refine ⟨(h.intervalIntegrable_capacity_iff _ ht).1 hi', ?_⟩
  have hs := h.integral_capacity_substitution (fun u => 2 / (v u - w u)) ht
  have hs' : (∫ u in (0 : ℝ)..t,
      2 * frzA W W' a φ 1 u ^ 2 / (V u - frzA W W' a φ 0 u)) =
      ∫ u in (0 : ℝ)..a t, 2 / (v u - w u) := by
    rw [← hs]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    dsimp only
    rw [hv u (hm u hu), hw u (hm u hu)]
    rw [sub_sub_sub_cancel_right]
    ring
  have h0 := hv 0 ⟨le_rfl, h.pos.le⟩
  rw [h.a0] at h0
  rw [hv t ht, h0, ← hs', he]
  ring

/-- The checked seed entrance equations supply the capacity equations and
reciprocal-gap integrability. No positive lower bound on a seed gap is used. -/
theorem SeedData.capacity_image_seed {n : ℕ} (s : SeedData n) {A : Set ℂ}
    {T r L₀ c : ℝ} {I : ℝ → Set ℝ} {w : ℝ → ℝ} {v : Fin n → ℝ → ℝ}
    (h : OwnData s.W A s.φ T s.a s.W') (hr : 0 < r)
    (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t))
    (hWI : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ I t)
    (hVI : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ I t)
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (Metric.ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t,
      deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hseed : ∀ m, IsSeedCoordinate s.W (s.V m) T)
    (hw : ∀ t ∈ Icc (0 : ℝ) T, w (s.a t) = s.A 0 t - c)
    (hv : ∀ m t, t ∈ Icc (0 : ℝ) T → v m (s.a t) = s.B0 t m - c)
    (m : Fin n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun u => (w u - v m u)⁻¹) volume 0 (s.a t) ∧
      v m (s.a t) = v m 0 + ∫ u in (0 : ℝ)..s.a t, 2 / (v m u - w u) := by
  exact h.capacity_force_equation ht hw (hv m)
    (s.imageEntranceIntegrable_of_seed h hr hI hWI hVI hclear hb hseed m t ht)
    (s.integrated_image_seed h hr hI hWI hVI hclear hb hseed m t ht)

end InteractingSLE.ZhanGT4
