/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInActCollar
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.Convex.Topology

/-!
# R.6: shared current-face collars from real contact order

PROVE-POCKET-SIDEIN. One access to the current component and absence of real
contacts along a connected interval imply half-disc access along the whole
interval. This supplies the geometric input to reflection, rather than
assuming reflection or inferring it from generic nesting of pockets.
-/

set_option autoImplicit false
noncomputable section

open Set Metric Topology
open QuantumZipper (H)
open scoped Pointwise

namespace InteractingSLE.Sec7.PocketStopSide

/-- A compact real segment avoiding a closed contact set has a connected
upper tube. A single access to the chosen current component puts this entire
tube, and hence a half-disc at its other endpoint, in the same component. -/
theorem exists_halfDisc_in_component_of_real_interval {Γ : Set ℂ} (hΓ : IsClosed Γ)
    {J : Set ℝ} (hJ : IsPreconnected J)
    (hContact : ∀ x ∈ J, (x : ℂ) ∉ Γ) {p : ℂ} {y₀ : ℝ}
    (hy₀ : y₀ ∈ J)
    (hAccess : (y₀ : ℂ) ∈ closure (connectedComponentIn (H \ Γ) p)) :
    ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ connectedComponentIn (H \ Γ) p := by
  intro x hx
  let K : Set ℂ := Complex.ofReal '' uIcc y₀ x
  have hKc : IsCompact K := isCompact_uIcc.image Complex.continuous_ofReal
  have hKaway : K ⊆ Γᶜ := by
    rintro z ⟨u, hu, rfl⟩
    exact hContact u (hJ.ordConnected.uIcc_subset hy₀ hx hu)
  obtain ⟨r, hr, htube⟩ := hKc.exists_thickening_subset_open hΓ.isOpen_compl hKaway
  have hKv : Convex ℝ K := (convex_uIcc y₀ x).linear_image Complex.ofRealLI.toLinearMap
  have hTv : Convex ℝ (thickening r K) := by
    rw [← add_ball_zero]
    exact hKv.add (convex_ball (0 : ℂ) r)
  obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.1 hAccess r hr
  have hzTube : z ∈ H ∩ thickening r K := by
    refine ⟨(connectedComponentIn_subset (H \ Γ) p hz).1, ?_⟩
    exact mem_thickening_iff.2 ⟨y₀, mem_image_of_mem _ left_mem_uIcc,
      (dist_comm _ _).trans_lt hdist⟩
  have hTubeAway : H ∩ thickening r K ⊆ H \ Γ := fun w hw => ⟨hw.1, htube hw.2⟩
  have hTubeComp := (convex_H.inter hTv).isPreconnected.subset_connectedComponentIn
    hzTube hTubeAway
  rw [← connectedComponentIn_eq hz] at hTubeComp
  refine ⟨r, hr, fun w hw => hTubeComp ⟨hw.1, ?_⟩⟩
  exact mem_thickening_iff.2 ⟨x, mem_image_of_mem _ right_mem_uIcc, hw.2⟩

/-- Finite next shared-side endpoint: the forbidden contacts are all to the
left of `q` or to the right of `pU`. The resulting shared interval includes
any driver strictly between these endpoints. -/
theorem exists_halfDisc_in_component_of_contact_order {Γ : Set ℂ} (hΓ : IsClosed Γ)
    {q pU y₀ : ℝ} {p : ℂ}
    (hContactOrder : ∀ u : ℝ, (u : ℂ) ∈ Γ → u ≤ q ∨ pU ≤ u)
    (hy₀ : y₀ ∈ Ioo q pU)
    (hAccess : (y₀ : ℂ) ∈ closure (connectedComponentIn (H \ Γ) p)) :
    ∀ x ∈ Ioo q pU, ∃ r > 0,
      H ∩ ball (x : ℂ) r ⊆ connectedComponentIn (H \ Γ) p := by
  apply exists_halfDisc_in_component_of_real_interval hΓ isPreconnected_Ioo
    (fun u hu hΓu => ?_) hy₀ hAccess
  rcases hContactOrder u hΓu with h | h
  · exact (not_le_of_gt hu.1) h
  · exact (not_le_of_gt hu.2) h

/-- The endpoint at infinity is permitted: no artificial finite right
endpoint is introduced in the current shared-face condition. -/
theorem exists_halfDisc_in_component_of_left_contacts {Γ : Set ℂ} (hΓ : IsClosed Γ)
    {q y₀ : ℝ} {p : ℂ}
    (hContactOrder : ∀ u : ℝ, (u : ℂ) ∈ Γ → u ≤ q)
    (hy₀ : q < y₀)
    (hAccess : (y₀ : ℂ) ∈ closure (connectedComponentIn (H \ Γ) p)) :
    ∀ x ∈ Ioi q, ∃ r > 0,
      H ∩ ball (x : ℂ) r ⊆ connectedComponentIn (H \ Γ) p := by
  exact exists_halfDisc_in_component_of_real_interval hΓ isPreconnected_Ioi
    (fun u hu hΓu => (not_le_of_gt hu) (hContactOrder u hΓu)) hy₀ hAccess

end InteractingSLE.Sec7.PocketStopSide
