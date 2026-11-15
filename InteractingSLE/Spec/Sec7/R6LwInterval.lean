/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6LwSelect
import InteractingSLE.Spec.Sec7.R6TsReflect
import InteractingSLE.Spec.Sec7.R6TsData

/-!
# Shared interval and force correspondence give same-time data

PROVE-R6-LANDING. Physical agreement at the current tip is explicit
local geometry, to be supplied by the inner-side construction. It is
not obtained from any assertion about current-tip fibers. The force
correspondence is a separate input supplied by incoming access.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Lw

open PocketStopSide

/-- **Named remaining physical interval geometry.** This contains no
singleton-fiber statement, selected tests, reflected boundary map, or
force correspondence. The tip ball and shared balls concern current
domains; there is no initial-pocket ball at the force landing. -/
structure PhysicalIncidentInterval (O I : Chart) (EO : ℂ → ℂ)
    (P : Set ℂ) (p : ℂ) (v : ℝ) where
  interval : Set ℝ
  isOpen : IsOpen interval
  isPreconnected : IsPreconnected interval
  force_mem : v ∈ interval
  driver_mem : 0 ∈ interval
  force_neg : v < 0
  inclusion : (I.dom : Set ℂ) ⊆ O.dom
  collars : ∀ x ∈ interval, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ O.1 '' (I.dom : Set ℂ)
  landing_mem : ∀ x ∈ interval, EO (x : ℂ) ∈ P
  force_ne_tip : EO (v : ℂ) ≠ p
  joint_access : ∀ ε > 0, ∃ z ∈ (I.dom : Set ℂ), ‖I.1 z‖ < ε ∧ ‖O.1 z‖ < ε
  tip_local : ∃ r > 0, (O.dom : Set ℂ) ∩ ball p r ⊆ I.dom
  shared_local : ∀ x ∈ interval, x < v →
    ∃ r > 0, (O.dom : Set ℂ) ∩ ball (EO (x : ℂ)) r ⊆ I.dom

/-- Joint fresh accesses in the two charts fix the reflected driver.
Equality of physical tip landings is not used to identify prime ends. -/
theorem driver_zero_of_joint_access
    {O I : Chart} (hO : O.IsConformal) (hI : I.IsConformal)
    (hIncl : (I.dom : Set ℂ) ⊆ O.dom) {g₀ : ℝ}
    (hlim : Tendsto (pocketTransitionChart O I).1
      (𝓝[((pocketTransitionChart O I).dom : Set ℂ)] 0) (𝓝 (g₀ : ℂ)))
    (haccess : ∀ ε > 0, ∃ z ∈ (I.dom : Set ℂ), ‖I.1 z‖ < ε ∧ ‖O.1 z‖ < ε) :
    g₀ = 0 := by
  by_contra hne
  have hd : 0 < |g₀| := abs_pos.2 hne
  obtain ⟨δ, hδ, hδlim⟩ := Metric.tendsto_nhdsWithin_nhds.1 hlim (|g₀| / 2) (half_pos hd)
  obtain ⟨z, hz, hzI, hzO⟩ := haccess (min δ (|g₀| / 2)) (lt_min hδ (half_pos hd))
  have hzT : O.1 z ∈ (pocketTransitionChart O I).dom := by
    rw [← SetLike.mem_coe, dom_pocketTransitionChart hO hI hIncl]
    exact mem_image_of_mem O.1 hz
  have hh := hδlim hzT (by
    rw [dist_zero_right]
    exact hzO.trans_le (min_le_left _ _))
  change dist (I.1 (O.2.1 (O.1 z))) (g₀ : ℂ) < |g₀| / 2 at hh
  rw [hO.inv_fwd (hIncl hz), dist_eq_norm] at hh
  have hn : ‖(g₀ : ℂ)‖ ≤ ‖I.1 z - (g₀ : ℂ)‖ + ‖I.1 z‖ := by
    have := norm_sub_le (I.1 z) (I.1 z - (g₀ : ℂ))
    rw [sub_sub_cancel] at this
    linarith [norm_sub_rev (I.1 z) (I.1 z - (g₀ : ℂ))]
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  linarith [min_le_right δ (|g₀| / 2)]

/-- The named physical interval and incoming force correspondence
give the exact `SameTimeLeftData`, with no use of Aux. 136. -/
theorem sameTimeLeftData_of_interval_and_force
    {V P : Set ℂ} {I : ℝ → Chart} {p : ℂ} (M : R6Tr.InnerChain V P I p)
    {O : Chart} (hO : O.IsConformal)
    {EO : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar) (hEO0 : EO 0 = p)
    {v : ℝ} (G : PhysicalIncidentInterval O (I M.time) EO P p v)
    (hforce : R6Ts.SharedForceIdentification O (I M.time) v (WangWu.chartAL M.driver M.time)) :
    Nonempty (R6Tr.SameTimeLeftData O (I M.time) EO P p v (WangWu.chartAL M.driver M.time)) := by
  obtain ⟨EI, hEI, hEIc⟩ := M.inverse_cont M.time M.time_mem
  obtain ⟨g, hg, -, -, hlim, hcanonical⟩ := R6Ts.real_transition_of_incident_collars
    M hO G.inclusion hEO hEOc hEI hEIc G.isOpen G.isPreconnected G.collars G.landing_mem
  have hg0 : g 0 = 0 := driver_zero_of_joint_access hO (M.conformal M.time M.time_mem)
    G.inclusion (by simpa only [Complex.ofReal_zero] using hlim 0 G.driver_mem) G.joint_access
  have hgv : g v = WangWu.chartAL M.driver M.time :=
    Complex.ofReal_injective ((hcanonical v G.force_mem).symm.trans hforce)
  exact sameTimeLeftData_of_local_interval G.inclusion hEOc hEO0 G.force_ne_tip
    G.isOpen G.isPreconnected G.force_mem G.driver_mem G.force_neg G.collars G.landing_mem
    hg hg0 hgv hlim G.tip_local G.shared_local

end InteractingSLE.Sec7.R6Lw
