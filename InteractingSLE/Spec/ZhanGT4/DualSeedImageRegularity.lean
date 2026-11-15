/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImageUniform

/-!
# Positive-time continuity of the seeded noise

Packet PROVE-ZHAN-GT4-A22. Only positive-time continuity is needed for a
predictable stopped integrand; the value at time zero may be chosen freely.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4
namespace SeedData

/-- The logarithmic noise is continuous at every positive own time,
including the stopping endpoint. -/
theorem continuousOn_ellX_driver {n : ℕ} (s : SeedData n) {A : Set ℂ}
    {T r L₀ Lrem : ℝ} {I : ℝ → Set ℝ}
    (h : OwnData s.W A s.φ T s.a s.W')
    {v₀ : ℝ → ℂ} (hv₀ : QuantumZipper.IsForwardSol s.W' s.ζ₀ (s.a T) v₀)
    (hr : 0 < r) (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t))
    (hWI : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ I t)
    (hVI : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ I t)
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t,
      deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hremote : ∀ t ∈ Icc (0 : ℝ) T, s.RemoteScale t Lrem)
    (hseed : ∀ m, IsSeedCoordinate s.W (s.V m) T)
    (hV₀c : ContinuousOn s.V₀ (Icc 0 T)) :
    ContinuousOn (fun t => s.ellX t (s.W t)) (Ioc 0 T) := by
  have nz : ∀ {u : ℝ}, InScale Lrem u → u ≠ 0 := by
    intro u hu he
    have hp := hu.1
    rw [he, abs_zero] at hp
    exact (not_le_of_gt (Real.exp_pos _)) hp
  have hrem : ∀ t ∈ Ioc (0 : ℝ) T,
      s.A 0 t - s.A20 t ≠ 0 ∧ s.W t - s.V₀ t ≠ 0 := by
    intro t ht
    exact div_ne_zero_iff.1 (nz (hremote t (Ioc_subset_Icc_self ht)).driver)
  have hB : ∀ m, ContinuousOn (fun t => s.B0 t m) (Ioc 0 T) := fun m =>
    (continuous_re.comp_continuousOn (h.continuousOn_iterDeriv_moving hr (hseed m).cont
      (fun t ht => hclear t ht _ (hVI t ht m)) 0)).mono Ioc_subset_Icc_self
  have hne : ∀ t ∈ Ioc (0 : ℝ) T, ∀ m, s.A 0 t - s.B0 t m ≠ 0 := by
    intro t ht m
    have ht' := Ioc_subset_Icc_self ht
    have hd : DifferentiableOn ℝ (s.F 0 t) (I t) := by
      intro x hx
      have hh := (h.ownExt_props ht' (hclear t ht' x hx)).1
      have hdx := hh.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
      exact hdx.hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt
    have hmono := strictMonoOn_of_deriv_pos (hI t ht') hd.continuousOn
      (fun x hx => (Real.exp_pos _).trans_le (hb t ht' x (interior_subset hx)).1)
    intro he
    have hi : s.F 0 t (s.W t) = s.F 0 t (s.V m t) := sub_eq_zero.1 he
    exact (hseed m).ne t ht (hmono.injOn (hVI t ht' m) (hWI t ht') hi.symm)
  have hy := continuousOn_dualLogSpaceX (κ := s.κ) (r := s.r)
    ((h.continuousOn_frzA 0).mono Ioc_subset_Icc_self)
    ((h.continuousOn_frzA 1).mono Ioc_subset_Icc_self)
    ((h.continuousOn_frzA 2).mono Ioc_subset_Icc_self)
    ((show ContinuousOn s.A20 (Icc 0 T) from fun t ht =>
      (h.hasDerivWithinAt_frzImg hv₀ ht).continuousWithinAt).mono Ioc_subset_Icc_self)
    hB (fun t ht => (h.frzA_one_pos (Ioc_subset_Icc_self ht)).ne')
    (fun t ht => (hrem t ht).1) hne
  have h0 := continuousOn_dualLogSpaceX (κ := s.κ) (r := s.r)
    (f1 := fun _ => 1) (f2 := fun _ => 0)
    (h.cont.continuousOn.mono Ioc_subset_Icc_self) continuousOn_const continuousOn_const
    (hV₀c.mono Ioc_subset_Icc_self) (fun m => (hseed m).cont.mono Ioc_subset_Icc_self)
    (fun _ _ => one_ne_zero) (fun t ht => (hrem t ht).2)
    (fun t ht m => sub_ne_zero.2 ((hseed m).ne t ht).symm)
  exact hy.sub h0

end SeedData
end InteractingSLE.ZhanGT4
