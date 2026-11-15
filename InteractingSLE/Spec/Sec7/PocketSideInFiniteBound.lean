/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRealContacts
import InteractingSLE.Foundations.Loewner.Capacity

/-!
# Local bounds for the actual current transition

PROVE-POCKET-SIDEIN. A finite initial-chart limit bounds the current map,
even when the initial coordinate is swallowed at the current time. Only
the existing uniform displacement estimate for the own Loewner map is used.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- A bounded input in the active domain has bounded current Loewner image.
No survival of the limiting boundary point is required. -/
theorem eventually_norm_bounded_loewner_comp {α : Type*} {l : Filter α}
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {f : α → ℂ} (hActive : ∀ᶠ z in l, f z ∈ H \ QuantumZipper.fwdHull W T)
    (hBound : ∃ M : ℝ, ∀ᶠ z in l, ‖f z‖ ≤ M) :
    ∃ M : ℝ, ∀ᶠ z in l, ‖QuantumZipper.fwdMap W T (f z)‖ ≤ M := by
  obtain ⟨B, -, hB⟩ := exists_abs_le_of_continuous hW T
  obtain ⟨M, hM⟩ := hBound
  refine ⟨M + (24 * B + 8 * Real.sqrt T), ?_⟩
  filter_upwards [hActive, hM] with z hz hm
  have hd := norm_fwdMap_sub_self_le hW hW0 hT hB hz ⟨hT, le_rfl⟩
  have hn := norm_sub_norm_le (QuantumZipper.fwdMap W T (f z)) (f z)
  linarith

/-- Membership in an actual own-current domain supplies the initial active
coordinate and the initial physical-domain membership. -/
theorem initial_coordinate_of_current_mem {c : Chart} (hc : c.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {p : ℂ} (hp : p ∈ (c.loewner W T).dom) :
    p ∈ c.dom ∧ c.1 p ∈ H \ QuantumZipper.fwdHull W T := by
  rw [← SetLike.mem_coe, (hc.loewner hW hW0 hT).coe_dom] at hp
  obtain ⟨z, hz, rfl⟩ := hp
  have hi := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT hz
  refine ⟨hc.inv_mem_dom hi.1, ?_⟩
  change c.1 (c.2.1 (QuantumZipper.fwdMapInv W T z)) ∈ _
  rwa [hc.2.2 _ hi.1]

/-- A finite initial inner-coordinate limit on a current outer access makes
the actual current transition locally bounded. This applies to exposed
accesses as well as to surviving incoming original-boundary accesses. -/
theorem eventually_norm_bounded_current_transition {outer initial : Chart}
    (hO : outer.IsConformal) (hInitial : initial.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hIncl : ((initial.loewner W T).dom : Set ℂ) ⊆ outer.dom)
    {x : ℝ} {b : ℂ}
    (hInitialLimit : Tendsto (fun z => initial.1 (outer.2.1 z))
      (𝓝[((pocketTransitionChart outer (initial.loewner W T)).dom : Set ℂ)] (x : ℂ))
      (𝓝 b)) :
    ∃ M : ℝ, ∀ᶠ z in
      𝓝[((pocketTransitionChart outer (initial.loewner W T)).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart outer (initial.loewner W T)).1 z‖ ≤ M := by
  have hActive : ∀ᶠ z in
      𝓝[((pocketTransitionChart outer (initial.loewner W T)).dom : Set ℂ)] (x : ℂ),
      initial.1 (outer.2.1 z) ∈ H \ QuantumZipper.fwdHull W T := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hp := (mem_dom_pocketTransitionChart hO (hInitial.loewner hW hW0 hT) hIncl).1 hz
    exact (initial_coordinate_of_current_mem hInitial hW hW0 hT hp.2).2
  apply eventually_norm_bounded_loewner_comp hW hW0 hT hActive
  refine ⟨‖b‖ + 1, ?_⟩
  filter_upwards [hInitialLimit.eventually (ball_mem_nhds b one_pos)] with z hz
  have hn := norm_sub_norm_le (initial.1 (outer.2.1 z)) b
  rw [dist_eq_norm] at hz
  linarith

/-- It suffices to identify the physical landing and a finite extension of
the initial inner chart there. The current map's boundary value is not an
input. -/
theorem eventually_norm_bounded_current_transition_of_landing {outer initial : Chart}
    (hO : outer.IsConformal) (hInitial : initial.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    (hIncl : ((initial.loewner W T).dom : Set ℂ) ⊆ outer.dom)
    {x : ℝ} {p : ℂ}
    (hLanding : Tendsto outer.2.1
      (𝓝[((pocketTransitionChart outer (initial.loewner W T)).dom : Set ℂ)] (x : ℂ)) (𝓝 p))
    {E : ℂ → ℂ} (hInitialEq : EqOn E initial.1 initial.dom)
    (hInitialContinuous : ContinuousWithinAt E initial.dom p) :
    ∃ M : ℝ, ∀ᶠ z in
      𝓝[((pocketTransitionChart outer (initial.loewner W T)).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart outer (initial.loewner W T)).1 z‖ ≤ M := by
  have hm : ∀ᶠ z in
      𝓝[((pocketTransitionChart outer (initial.loewner W T)).dom : Set ℂ)] (x : ℂ),
      outer.2.1 z ∈ initial.dom := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hp := (mem_dom_pocketTransitionChart hO (hInitial.loewner hW hW0 hT) hIncl).1 hz
    exact (initial_coordinate_of_current_mem hInitial hW hW0 hT hp.2).1
  have hlim := hInitialContinuous.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hLanding, hm⟩)
  apply eventually_norm_bounded_current_transition hO hInitial hW hW0 hT hIncl
  exact hlim.congr' (hm.mono fun z hz => hInitialEq hz)

end InteractingSLE.Sec7.PocketStopSide
