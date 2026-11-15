/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExit
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov

/-!
# GW1: D.4's filled upper collar and exclusion of middle real contacts

The landed path-crossing theorem already applies to arbitrary continuous half-plane
prefixes, including prefixes ending in the interior. Together with the boundary-of-filling
lemma it gives the collar required in R53 D.4 without a real-endpoint restriction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.GW1WalkExit

theorem notMem_closure_active_of_between_contacts {γ : ℝ → ℂ} {T : ℝ}
    (hc : ContinuousOn γ (Icc 0 T)) (hH : MapsTo γ (Icc 0 T) Hbar)
    {u v : ℝ} (hu : u ∈ Icc 0 T) (hv : v ∈ Icc 0 T)
    (huR : (γ u).im = 0) (hvR : (γ v).im = 0) {x : ℝ}
    (hux : (γ u).re < x) (hxv : x < (γ v).re)
    (hx : (x : ℂ) ∉ γ '' Icc 0 T) :
    (x : ℂ) ∉ closure (H \ fillH (γ '' Icc 0 T)) := by
  have hfill := YuanCharacterisation.mem_closure_fillH_of_lt_of_lt hc hH hu hv huR hvR hux hxv hx
  intro hactive
  apply hx
  apply YuanCharacterisation.mem_of_mem_closure_of_mem_frontier
    (isCompact_Icc.image_of_continuousOn hc).isClosed (by simp) hfill
  refine ⟨hactive, ?_⟩
  intro hi
  have h := interior_subset hi
  have hxH : 0 < (x : ℂ).im := h.1
  simp only [Complex.ofReal_im, lt_self_iff_false] at hxH

/-- The filled upper half-neighborhood of an untraced point between real contacts.
No assertion that the prefix ends on the real line is needed. -/
theorem exists_upperCollar_fillH {γ : ℝ → ℂ} {T : ℝ}
    (hc : ContinuousOn γ (Icc 0 T)) (hH : MapsTo γ (Icc 0 T) Hbar)
    {u v : ℝ} (hu : u ∈ Icc 0 T) (hv : v ∈ Icc 0 T)
    (huR : (γ u).im = 0) (hvR : (γ v).im = 0) {x : ℝ}
    (hux : (γ u).re < x) (hxv : x < (γ v).re)
    (hx : (x : ℂ) ∉ γ '' Icc 0 T) :
    ∃ ε > 0, ball (x : ℂ) ε ∩ H ⊆ fillH (γ '' Icc 0 T) := by
  have hfree := notMem_closure_active_of_between_contacts hc hH hu hv huR hvR hux hxv hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (isClosed_closure.isOpen_compl.mem_nhds hfree)
  refine ⟨ε, hε, fun z hz => ?_⟩
  by_contra hn
  exact hball hz.1 (subset_closure (show z ∈ H \ fillH (γ '' Icc 0 T) from ⟨hz.2, hn⟩))

/-- A new accessible real point avoiding the old raw prefix is a strict new extreme.
This is the real-contact assertion used by D.4, with accessibility stated topologically. -/
theorem new_real_contact_is_extreme {γ : ℝ → ℂ} {T : ℝ}
    (hc : ContinuousOn γ (Icc 0 T)) (hH : MapsTo γ (Icc 0 T) Hbar)
    {u v L R x : ℝ} (hu : u ∈ Icc 0 T) (hv : v ∈ Icc 0 T)
    (huL : γ u = (L : ℂ)) (hvR : γ v = (R : ℂ))
    (hx : (x : ℂ) ∉ γ '' Icc 0 T)
    (hactive : (x : ℂ) ∈ closure (H \ fillH (γ '' Icc 0 T))) :
    x < L ∨ R < x := by
  by_contra hn
  have hL : L ≤ x := le_of_not_gt (fun h => hn (Or.inl h))
  have hR : x ≤ R := le_of_not_gt (fun h => hn (Or.inr h))
  have hLx : L < x := lt_of_le_of_ne hL (fun he => hx ⟨u, hu, huL.trans (congrArg _ he)⟩)
  have hxR : x < R := lt_of_le_of_ne hR (fun he => hx ⟨v, hv, hvR.trans (congrArg _ he.symm)⟩)
  apply notMem_closure_active_of_between_contacts hc hH hu hv
    (by rw [huL]; simp) (by rw [hvR]; simp) ?_ ?_ hx hactive
  · simpa only [huL, Complex.ofReal_re] using hLx
  · simpa only [hvR, Complex.ofReal_re] using hxR

end InteractingSLE.Theorem14.GW1WalkExit
