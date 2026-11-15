/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImagePrepare

/-!
# Integrated image force equations for seed marks

Packet PROVE-ZHAN-GT4-A22. Reuse the landed moving-mark chain rule.
Divided-difference cancellation supplies entrance integrability, so the
image equations hold from zero without a new entrance hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4

/-- A uniform moving clear disc gives a fixed clear disc for nearby times.
This specializes the continuity argument of `SeedData.exists_mark_clear`
without its unrelated band-scale hypotheses. -/
theorem exists_fixed_seed_clear {W V : ℝ → ℝ} {A : Set ℂ} {T r t : ℝ}
    (hr : 0 < r) (hc : ContinuousOn V (Icc 0 T))
    (hclear : ∀ u ∈ Icc (0 : ℝ) T, Disjoint (ball (V u : ℂ) r)
      ((fun z => QuantumZipper.fwdMap W u z + W u) '' A)) (ht : t ∈ Icc (0 : ℝ) T) :
    ∃ ρ > (0 : ℝ), ∃ η > (0 : ℝ), ∀ u ∈ Icc (max 0 (t - η)) (min T (t + η)),
      Disjoint (ball (V t : ℂ) ρ) ((fun z => QuantumZipper.fwdMap W u z + W u) '' A) := by
  obtain ⟨δ, hδ, hδV⟩ := Metric.continuousOn_iff.1 hc t ht (r / 2) (by positivity)
  refine ⟨r / 2, by positivity, δ / 2, by positivity, fun u hu => ?_⟩
  obtain ⟨hu0, hut⟩ := OwnData.mem_box_of_abs_lt (T := T) hu
  have hV := hδV u hu0 (by rw [Real.dist_eq]; linarith only [hut, hδ])
  rw [Real.dist_eq] at hV
  refine (hclear u hu0).mono_left fun z hz => ?_
  rw [mem_ball, dist_eq_norm] at hz ⊢
  have he : ‖(V t : ℂ) - V u‖ < r / 2 := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hV
  have htri := norm_add_le (z - V t) ((V t : ℂ) - V u)
  rw [sub_add_sub_cancel] at htri
  linarith only [hz, he, htri]

namespace SeedData

/-- The image mark equation holds on the full positive-time lifetime
interval, with no fixed positive seed gap. -/
theorem hasDerivWithinAt_image_seed {n : ℕ} (s : SeedData n) {A : Set ℂ}
    {T r L₀ : ℝ} {I : ℝ → Set ℝ}
    (h : OwnData s.W A s.φ T s.a s.W') (hr : 0 < r)
    (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t))
    (hWI : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ I t)
    (hVI : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ I t)
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t,
      deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hseed : ∀ m, IsSeedCoordinate s.W (s.V m) T) (m : Fin n) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) T) :
    HasDerivWithinAt (fun u => s.B0 u m)
      (2 * s.A 1 t ^ 2 / (s.B0 t m - s.A 0 t)) (Ioc 0 T) t := by
  have ht' := Ioc_subset_Icc_self ht
  have hd : DifferentiableOn ℝ (s.F 0 t) (I t) := by
    intro x hx
    have hh := (h.ownExt_props ht' (hclear t ht' x hx)).1
    have hdx := hh.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    exact hdx.hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt
  have hmono := strictMonoOn_of_deriv_pos (hI t ht') hd.continuousOn
    (fun x hx => (Real.exp_pos _).trans_le (hb t ht' x (interior_subset hx)).1)
  have hne : s.B0 t m ≠ s.A 0 t := fun he =>
    (hseed m).ne t ht (hmono.injOn (hVI t ht' m) (hWI t ht') he)
  have he0 : s.A 0 t = s.W' (s.a t) := h.frzA_zero ht'
  have hVF : (ownExt s.W s.W' s.a s.φ t (s.V m t)).re ≠ s.W' (s.a t) := by
    rwa [← he0]
  obtain ⟨ρ, hρ, η, hη, hcl⟩ := exists_fixed_seed_clear hr (hseed m).cont
    (fun u hu => hclear u hu _ (hVI u hu m)) ht'
  rw [he0]
  exact h.hasDerivWithinAt_markVal Ioc_subset_Icc_self ht'
    ((hseed m).hasDerivWithinAt_pos h.cont ht) hρ hη hcl ((hseed m).ne t ht) hVF

/-- The image seed satisfies its integrated force equation from time zero.
The original seed equation supplies entrance integrability internally. -/
theorem integrated_image_seed {n : ℕ} (s : SeedData n) {A : Set ℂ}
    {T r L₀ : ℝ} {I : ℝ → Set ℝ}
    (h : OwnData s.W A s.φ T s.a s.W') (hr : 0 < r)
    (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t))
    (hWI : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ I t)
    (hVI : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ I t)
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t,
      deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hseed : ∀ m, IsSeedCoordinate s.W (s.V m) T) :
    ∀ m t, t ∈ Icc (0 : ℝ) T → s.B0 t m = s.B0 0 m +
      ∫ u in (0 : ℝ)..t, 2 * s.A 1 u ^ 2 / (s.B0 u m - s.A 0 u) := by
  apply s.integrated_image_marks
  · intro m
    exact continuous_re.comp_continuousOn (h.continuousOn_iterDeriv_moving hr (hseed m).cont
      (fun u hu => hclear u hu _ (hVI u hu m)) 0)
  · exact s.hasDerivWithinAt_image_seed h hr hI hWI hVI hclear hb hseed
  · exact s.imageEntranceIntegrable_of_seed h hr hI hWI hVI hclear hb hseed

end SeedData
end InteractingSLE.ZhanGT4
