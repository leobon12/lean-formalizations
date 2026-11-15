/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTailLimit
import InteractingSLE.Spec.Sec7.PocketSideInFiniteLanding

/-!
# Bounded old coordinates along a current pocket approach

PROVE-POCKET-SIDEIN. The initial Jordan coordinate is finite away from
the outgoing corner. Its bounded input and the existing Loewner displacement
estimate bound the old coordinate, even if the physical landing is swallowed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

/-- Finite initial coordinates bound the older Loewner coordinate along
a nested current inverse. No survival of the limiting boundary point is assumed. -/
theorem eventually_norm_bounded_old_coordinate {initial current : Chart}
    (hInitial : initial.IsConformal) (hCurrent : current.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    (hInclusion : (current.dom : Set ℂ) ⊆ (initial.loewner W q).dom)
    {ξ : ℝ} {p : ℂ} (hLanding : Tendsto current.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p))
    {E : ℂ → ℂ} (hE : EqOn E initial.1 initial.dom)
    (hEc : ContinuousWithinAt E initial.dom p) :
    ∃ M : ℝ, ∀ᶠ z in 𝓝[H] (ξ : ℂ),
      ‖(initial.loewner W q).1 (current.2.1 z)‖ ≤ M := by
  have hActive : ∀ z ∈ H, current.2.1 z ∈ initial.dom ∧
      initial.1 (current.2.1 z) ∈ H \ QuantumZipper.fwdHull W q :=
    fun z hz => initial_coordinate_of_current_mem hInitial hW hW0 hq
      (hInclusion (hCurrent.inv_mem_dom hz))
  have hPhysical : Tendsto current.2.1 (𝓝[H] (ξ : ℂ)) (𝓝[initial.dom] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hLanding,
      eventually_nhdsWithin_of_forall fun z hz => (hActive z hz).1⟩
  have hLimit : Tendsto (fun z => initial.1 (current.2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (E p)) :=
    (hEc.tendsto.comp hPhysical).congr'
      (eventually_nhdsWithin_of_forall fun z hz => hE (hActive z hz).1)
  apply eventually_norm_bounded_loewner_comp hW hW0 hq
    (eventually_nhdsWithin_of_forall fun z hz => (hActive z hz).2)
  refine ⟨‖E p‖ + 1, ?_⟩
  filter_upwards [hLimit.eventually (ball_mem_nhds (E p) one_pos)] with z hz
  have hn := norm_sub_norm_le (initial.1 (current.2.1 z)) (E p)
  rw [dist_eq_norm] at hz
  linarith

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C
  Sec7.PocketCoord Sec7.PocketJordan

variable {Ω : Type} [MeasurableSpace Ω]

/-- Construct the correct real old access of the actual pocket. The
only boundary-location input is exclusion from that old physical domain. -/
theorem exists_actual_old_incident_access {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event)
    (hTrace : IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω))
    {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T)
    (hVisitS : d.curve ω s ∈ (j.target i d).domain ω)
    (hVisitT : d.curve ω T ∈ (j.target i d).domain ω) {ξ : ℝ}
    (hBoundary : j.currentVisitLanding i d ω T ξ ∉ (j.referenceVisitChart i d ω s).dom)
    (hNotExit : j.infinite = false → j.currentVisitLanding i d ω T ξ ≠
      cfPt (openPt (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))) :
    ∃ x : ℝ,
      Tendsto (fun z => (j.referenceVisitChart i d ω s).1
        ((j.referenceVisitChart i d ω T).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Tendsto (j.referenceVisitChart i d ω s).2.1 (𝓝[H] (x : ℂ))
        (𝓝 (j.currentVisitLanding i d ω T ξ)) := by
  have hOld := isDomainChart_referenceVisitChart hj hRc hLc hω hTrace hs hVisitS
  have hNow := isDomainChart_referenceVisitChart hj hRc hLc hω hTrace (hs.trans hsT) hVisitT
  have hIncl : ((j.referenceVisitChart i d ω T).dom : Set ℂ) ⊆
      (j.referenceVisitChart i d ω s).dom := by
    rw [hNow.coe_dom, hOld.coe_dom]
    exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2
      (fillH_mono (image_mono (Icc_subset_Icc_right hsT)) h)⟩
  obtain ⟨hE, hEc, -⟩ := currentVisitLanding_spec hj hRc hLc hω hs hVisitS
  have hLanding := tendsto_currentVisitLanding hj hRc hLc hω (hs.trans hsT) hVisitT ξ
  apply exists_old_incident_access_of_inverse_extension hOld.1 hNow.1 hIncl hE hEc hLanding hBoundary
  have hBase := isDomainChart_baseChart hj hRc hLc hω
  obtain ⟨W, hW, hW0, _, _, _, hOldEq⟩ := exists_relChart_eq_loewner
    (c := (j.target i d).baseChart) (isDrivenCurve_target hj ω hω)
    (visitCapacity_spec hj hω hs hVisitS).2.1
  change j.referenceVisitChart i d ω s = _ at hOldEq
  obtain ⟨E, hInitialE, hInitialEc⟩ := exists_initial_finite_extension_of_ready hj hRc hLc hω
    ((currentVisitLanding_spec hj hRc hLc hω (hs.trans hsT) hVisitT).2.2
      (mem_Hbar_of_im_eq_zero (by simp : (ξ : ℂ).im = 0))) hNotExit
  rw [hOldEq] at hIncl ⊢
  exact eventually_norm_bounded_old_coordinate hBase.1 hNow.1 hW hW0
    (j.visitCapacity d ω s).toNNReal.coe_nonneg hIncl hLanding hInitialE hInitialEc

end InteractingSLE.Wire.Current.SideTest
