/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInInstCharts
import InteractingSLE.Spec.Supplement.GB11ChartBdryPlanar

/-!
# Current relative-face geometry for nested actual pocket charts

PROVE-POCKET-SIDEIN. The relative domain is constructed from the two current
charts. Its frontier and disjointness data identify the actual complement
component. The source contact ordering then gives a shared interval through
the current driver. The frontier/contact producers remain named inputs.
-/

set_option autoImplicit false
noncomputable section

open Set Metric Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- A current chart's domain is the selected component when its interior
frontier is accounted for by the retained closed contact set. -/
theorem current_face_eq_component_of_frontier {c : Chart} (hc : c.IsConformal)
    {Γ : Set ℂ} (hContactAway : Disjoint (c.dom : Set ℂ) Γ)
    (hCurrentFrontier : frontier (c.dom : Set ℂ) ∩ H ⊆ Γ)
    {p : ℂ} (hp : p ∈ c.dom) :
    (c.dom : Set ℂ) = connectedComponentIn (H \ Γ) p := by
  have hpre : IsPreconnected (c.dom : Set ℂ) := by
    rw [hc.coe_dom]
    exact convex_H.isPreconnected.image _ hc.1.continuousOn
  have hsub : (c.dom : Set ℂ) ⊆ H \ Γ := fun z hz =>
    ⟨hc.dom_subset hz, fun hzΓ => disjoint_left.1 hContactAway hz hzΓ⟩
  have hfr : frontier (c.dom : Set ℂ) ⊆ (H \ Γ)ᶜ := by
    intro z hz hzD
    exact hzD.2 (hCurrentFrontier ⟨hz, hzD.1⟩)
  simpa only [compl_compl] using
    (Theorem14.GB11Chart.eq_connectedComponentIn_of_frontier_subset c.dom.isOpen hpre hp
      (F := (H \ Γ)ᶜ) (fun _ hz h => h (hsub hz)) hfr).symm

/-- The source's actual relative frontier and real contact order supply the
shared collars; the current-component identity is no longer a premise. -/
theorem shared_collars_pocketTransitionChart {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {Γ : Set ℂ} (hΓ : IsClosed Γ)
    (hContactAway : Disjoint (outer.1 '' (inner.dom : Set ℂ)) Γ)
    (hCurrentFrontier : frontier (outer.1 '' (inner.dom : Set ℂ)) ∩ H ⊆ Γ)
    {J : Set ℝ} (hJ : IsPreconnected J) (hContact : ∀ x ∈ J, (x : ℂ) ∉ Γ)
    {y₀ : ℝ} (hy₀ : y₀ ∈ J)
    (hSharedAccess : (y₀ : ℂ) ∈ closure (outer.1 '' (inner.dom : Set ℂ))) :
    ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ) := by
  let c := pocketTransitionChart outer inner
  have hc : c.IsConformal := isConformal_pocketTransitionChart hO hI hCurrentInclusion
  have he : (c.dom : Set ℂ) = outer.1 '' (inner.dom : Set ℂ) :=
    dom_pocketTransitionChart hO hI hCurrentInclusion
  have hp : c.2.1 Complex.I ∈ c.dom := hc.inv_mem_dom (by show 0 < Complex.I.im; norm_num)
  have hcomp := current_face_eq_component_of_frontier hc (he.symm ▸ hContactAway)
    (he.symm ▸ hCurrentFrontier) hp
  have hAccess : (y₀ : ℂ) ∈ closure (connectedComponentIn (H \ Γ) (c.2.1 Complex.I)) := by
    rw [← hcomp, he]
    exact hSharedAccess
  rw [hcomp]
  exact exists_halfDisc_in_component_of_real_interval hΓ hJ hContact hy₀ hAccess

/-- Astra's mixed-pocket ordering `VL ≤ qβ < W < pU` gives the actual
shared interval through the driver. Other real contacts lie on the two
outside pieces; the contact at `qβ` itself is allowed. -/
theorem shared_interval_of_mixed_contact_order {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom)
    {Γ : Set ℂ} (hΓ : IsClosed Γ)
    (hContactAway : Disjoint (outer.1 '' (inner.dom : Set ℂ)) Γ)
    (hCurrentFrontier : frontier (outer.1 '' (inner.dom : Set ℂ)) ∩ H ⊆ Γ)
    {VL qβ W pU y₀ : ℝ} (hVL : VL ≤ qβ) (hqW : qβ < W) (hWp : W < pU)
    (hActualContacts : ∀ x : ℝ, (x : ℂ) ∈ Γ → x ≤ VL ∨ x = qβ ∨ pU ≤ x)
    (hy₀ : y₀ ∈ Ioo qβ pU)
    (hSharedAccess : (y₀ : ℂ) ∈ closure (outer.1 '' (inner.dom : Set ℂ))) :
    W ∈ Ioo qβ pU ∧ ∀ x ∈ Ioo qβ pU, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ) := by
  refine ⟨⟨hqW, hWp⟩, shared_collars_pocketTransitionChart hO hI hCurrentInclusion hΓ
    hContactAway hCurrentFrontier isPreconnected_Ioo (fun x hx hxc => ?_) hy₀ hSharedAccess⟩
  rcases hActualContacts x hxc with h | h | h
  · exact (not_le_of_gt hx.1) (h.trans hVL)
  · exact (ne_of_gt hx.1) h
  · exact (not_le_of_gt hx.2) h

end InteractingSLE.Sec7.PocketStopSide
