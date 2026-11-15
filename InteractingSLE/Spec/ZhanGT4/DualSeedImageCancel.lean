/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteEntrance
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteGirsanov
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-!
# Cancellation in the seeded logarithmic noise

Packet PROVE-ZHAN-GT4-A22. A positive first derivative and a bounded second
derivative bound the difference of the image and original reciprocal gaps,
uniformly as a seed gap tends to zero.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

/-- A divided difference is a derivative at a point of the joining interval. -/
theorem exists_dslope_eq_deriv_on_interval {f : ℝ → ℝ} {I : Set ℝ}
    (hI : Convex ℝ I) (hf : DifferentiableOn ℝ f I) {u v : ℝ}
    (hu : u ∈ I) (hv : v ∈ I) :
    ∃ x ∈ uIcc u v, dslope f u v = deriv f x := by
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · have hs : Icc u v ⊆ I := hI.ordConnected.out hu hv
    obtain ⟨x, hx, he⟩ := exists_deriv_eq_slope f hlt
      (hf.continuousOn.mono hs) (hf.mono (Ioo_subset_Icc_self.trans hs))
    refine ⟨x, Icc_subset_uIcc (Ioo_subset_Icc_self hx), ?_⟩
    rw [dslope_of_ne _ hlt.ne', slope_def_field, he]
  · exact ⟨u, left_mem_uIcc, dslope_same _ _⟩
  · have hs : Icc v u ⊆ I := hI.ordConnected.out hv hu
    obtain ⟨x, hx, he⟩ := exists_deriv_eq_slope f hgt
      (hf.continuousOn.mono hs) (hf.mono (Ioo_subset_Icc_self.trans hs))
    refine ⟨x, ?_, ?_⟩
    · rw [uIcc_comm]
      exact Icc_subset_uIcc (Ioo_subset_Icc_self hx)
    · rw [dslope_of_ne _ hgt.ne, slope_comm, slope_def_field, he]

/-- The difference of reciprocal gaps stays bounded when the seed gap closes.
The coincident case is valid with Lean's zero-division convention as well. -/
theorem abs_reciprocal_cancel_le {f f₁ f₂ : ℝ → ℝ} {I : Set ℝ}
    (hI : Convex ℝ I) (hf : ∀ x ∈ I, HasDerivAt f (f₁ x) x)
    (hf₁ : ∀ x ∈ I, HasDerivAt f₁ (f₂ x) x)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hl : ∀ x ∈ I, c ≤ f₁ x) (hb : ∀ x ∈ I, |f₂ x| ≤ M)
    {u v : ℝ} (hu : u ∈ I) (hv : v ∈ I) :
    |f₁ u / (f u - f v) - 1 / (u - v)| ≤ M / c := by
  by_cases he : u = v
  · subst v
    simpa only [sub_self, div_zero, abs_zero] using div_nonneg hM hc.le
  obtain ⟨x, hx, hxe⟩ := exists_dslope_eq_deriv_on_interval hI
    (fun y hy => (hf y hy).differentiableAt.differentiableWithinAt) hu hv
  have hxI : x ∈ I := hI.ordConnected.uIcc_subset hu hv hx
  have hd : dslope f u v = f₁ x := hxe.trans (hf x hxI).deriv
  have hds : c ≤ dslope f u v := by rw [hd]; exact hl x hxI
  have hds0 := hc.trans_le hds
  have hdist : |u - x| ≤ |u - v| := by
    simpa only [Real.dist_eq] using Real.dist_left_le_of_mem_uIcc hx
  have hmv := hI.norm_image_sub_le_of_norm_deriv_le
    (fun y hy => (hf₁ y hy).differentiableAt)
    (fun y hy => by rw [(hf₁ y hy).deriv, Real.norm_eq_abs]; exact hb y hy) hxI hu
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
  have hn : |f₁ u - dslope f u v| ≤ M * |u - v| := by
    rw [hd]
    exact hmv.trans (mul_le_mul_of_nonneg_left hdist hM)
  have heq : f₁ u / (f u - f v) - 1 / (u - v) =
      (f₁ u - dslope f u v) / (u - v) / dslope f u v := by
    have hsl := sub_smul_dslope f u v
    simp only [smul_eq_mul] at hsl
    have hsub : f u - f v = (u - v) * dslope f u v := by nlinarith only [hsl]
    rw [hsub]
    field_simp [sub_ne_zero.2 he, hds0.ne']
  rw [heq, abs_div, abs_div, abs_of_pos hds0]
  have hn' : |f₁ u - dslope f u v| / |u - v| ≤ M :=
    (div_le_iff₀ (abs_pos.2 (sub_ne_zero.2 he))).2 hn
  exact (div_le_div_of_nonneg_right hn' hds0.le).trans
    (div_le_div_of_nonneg_left hM hc hds)

end InteractingSLE.ZhanGT4
