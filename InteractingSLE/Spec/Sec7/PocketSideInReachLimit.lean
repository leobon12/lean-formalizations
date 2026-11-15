/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInReachLocal

/-!
# Finite transition limits from the existing inverse extension

PROVE-POCKET-SIDEIN. A current inner inverse already extends continuously
to Hbar. Its real boundary values cannot lie in its open domain. The
localized inverse-fibre cluster theorem therefore constructs finite real
limits of a locally bounded transition on a shared current half-disc.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The real values of any continuous inverse extension avoid its interior
image. This is the landed real inverse-landing theorem, with no extra trace
or injectivity assumption at the physical boundary. -/
theorem inverse_extension_real_notMem_image {c : Chart} (hc : c.IsConformal)
    {E : ℂ → ℂ} (hE : EqOn E c.2.1 H) (hEc : ContinuousOn E Hbar) :
    ∀ z : ℂ, z.im = 0 → E z ∉ E '' H := by
  intro z hz0
  have hzbar : z ∈ Hbar := mem_Hbar_of_im_eq_zero hz0
  have hlim : Tendsto c.2.1 (𝓝[H] z) (𝓝 (E z)) :=
    (((hEc z hzbar).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hw => hE hw)
  have hreal : (z.re : ℂ) = z := (eq_ofReal_re_of_im_eq_zero hz0).symm
  have hnot : E z ∉ c.dom := inverse_real_landing_notMem_dom hc
    (x := z.re) (by simpa only [hreal] using hlim)
  rintro ⟨w, hw, hweq⟩
  apply hnot
  rw [← hweq, hE hw]
  exact hc.inv_mem_dom hw

/-- The current transition has a finite real limit whenever its physical
outer landing exists, it has a shared half-disc, and it is locally bounded.
The real target coordinate is constructed from the actual inner inverse. -/
theorem exists_real_transition_limit_of_local_bound {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hIncl : (inner.dom : Set ℂ) ⊆ outer.dom) {E : ℂ → ℂ}
    (hE : EqOn E inner.2.1 H) (hEc : ContinuousOn E Hbar)
    {x r : ℝ} (hr : 0 < r)
    (hCollar : H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ))
    {p : ℂ} (hLanding : Tendsto outer.2.1 (𝓝[H] (x : ℂ)) (𝓝 p))
    (hBound : ∃ M : ℝ, ∀ᶠ z in
      𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart outer inner).1 z‖ ≤ M) :
    ∃ y : ℝ, E y = p ∧ Tendsto (pocketTransitionChart outer inner).1
      (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) := by
  have hc := isConformal_pocketTransitionChart hO hI hIncl
  have hDom : ((pocketTransitionChart outer inner).dom : Set ℂ) ∈ 𝓝[H] (x : ℂ) := by
    apply mem_of_superset (inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hr))
    exact hCollar
  have hWithin : 𝓝[H] (x : ℂ) ≤
      𝓝[((pocketTransitionChart outer inner).dom : Set ℂ)] (x : ℂ) :=
    nhdsWithin_le_of_mem hDom
  have hComposite : Tendsto (fun z => E ((pocketTransitionChart outer inner).1 z))
      (𝓝[H] (x : ℂ)) (𝓝 p) := by
    refine hLanding.congr' ?_
    filter_upwards [hDom] with z hz
    have hp := (mem_dom_pocketTransitionChart hO hI hIncl).1 hz
    exact (hE (hI.fwd_mem hp.2)).trans (hI.inv_fwd hp.2) |>.symm
  obtain ⟨M, hM⟩ := hBound
  obtain ⟨y, hy, hEy, hlim⟩ := exists_tendsto_of_tendsto_comp_local
    (hI.1.congr (fun _ hz => hE hz)) hEc
    (hI.injOn.congr hE.symm) (inverse_extension_real_notMem_image hI hE hEc) hr
    (hc.differentiableOn_fwd.continuousOn.mono hCollar)
    (fun _ hz => QuantumZipper.H_subset_Hbar (hc.fwd_mem (hCollar hz)))
    (hWithin hM) hComposite
  have hy0 : y.im = 0 := by
    apply le_antisymm ?_ hy
    apply le_of_not_gt
    intro hyH
    apply inverse_real_landing_notMem_dom hO hLanding
    apply hIncl
    rw [← hEy, hE hyH]
    exact hI.inv_mem_dom hyH
  have hyreal : (y.re : ℂ) = y := (eq_ofReal_re_of_im_eq_zero hy0).symm
  exact ⟨y.re, by rwa [hyreal], by rwa [hyreal]⟩

end InteractingSLE.Sec7.PocketStopSide
