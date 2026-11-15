/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteD10
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteRegularity

/-!
# Image force integrability at a seed entrance

Packet PROVE-ZHAN-GT4-A22. Cancel the image gap against a divided
difference before integrating. The resulting continuous factor multiplies
the original integrable seed force, so no driving-law approximation is used.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4

/-- The cancelled image-force rate, valid also when both coordinates meet. -/
theorem image_force_rate_eq_dslope (f : ℝ → ℝ) (u v a : ℝ) :
    2 * a ^ 2 / (f v - f u) = (2 / (v - u)) * (a ^ 2 / dslope f u v) := by
  by_cases he : v = u
  · simp [he]
  · rw [dslope_of_ne _ he, slope_def_field]
    by_cases hf : f v - f u = 0
    · simp [hf]
    · field_simp [sub_ne_zero.2 he, hf]

namespace SeedData

/-- The image entrance rate is integrable because the original seed rate
is integrable and the cancelled divided-difference factor is continuous. -/
theorem imageEntranceIntegrable_of_seed {n : ℕ} (s : SeedData n)
    {A : Set ℂ} {T r L₀ : ℝ} {I : ℝ → Set ℝ}
    (h : OwnData s.W A s.φ T s.a s.W') (hr : 0 < r)
    (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t))
    (hWI : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ I t)
    (hVI : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ I t)
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t,
      deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hseed : ∀ m, IsSeedCoordinate s.W (s.V m) T) : s.ImageEntranceIntegrable T := by
  intro m t ht
  have hds : ContinuousOn (fun u => dslope (s.F 0 u) (s.W u) (s.V m u)) (Icc 0 T) :=
    h.continuousOn_dslope_moving hr h.cont.continuousOn (hseed m).cont
      (fun u hu => hclear u hu _ (hWI u hu)) (fun u hu => hclear u hu _ (hVI u hu m))
  have hdsne : ∀ u ∈ Icc (0 : ℝ) T, dslope (s.F 0 u) (s.W u) (s.V m u) ≠ 0 := by
    intro u hu
    have hd : DifferentiableOn ℝ (s.F 0 u) (I u) := by
      intro x hx
      have hf := (h.ownExt_props hu (hclear u hu x hx)).1
      have hfx := hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
      exact hfx.hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt
    have hs := inScale_dslope_of_deriv_bounds (hI u hu) hd (hb u hu) (hWI u hu) (hVI u hu m)
    intro he
    have hh := hs.1
    rw [he, abs_zero] at hh
    exact (not_le_of_gt (Real.exp_pos _)) hh
  have hfac : ContinuousOn (fun u => s.A 1 u ^ 2 / dslope (s.F 0 u) (s.W u) (s.V m u)) (Icc 0 T) :=
    (h.continuousOn_frzA 1 |>.pow 2).div hds hdsne
  have hi := (hseed m).integrable t ht |>.mul_continuousOn
    (by rw [uIcc_of_le ht.1]; exact hfac.mono (Icc_subset_Icc_right ht.2))
  have he : (fun u => 2 * s.A 1 u ^ 2 / (s.B0 u m - s.A 0 u)) =
      fun u => (2 / (s.V m u - s.W u)) *
        (s.A 1 u ^ 2 / dslope (s.F 0 u) (s.W u) (s.V m u)) := by
    funext u
    exact image_force_rate_eq_dslope (s.F 0 u) (s.W u) (s.V m u) (s.A 1 u)
  rw [he]
  exact hi

end SeedData

end InteractingSLE.ZhanGT4
