/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTailBound
import InteractingSLE.Spec.Sec7.PocketSideInTailPast
import InteractingSLE.Spec.Sec7.PocketSideInExitLanding

/-!
# The old incident collar at an actual current boundary landing

PROVE-POCKET-SIDEIN. The physical frontier locates the point on an old
prefix or the initial pocket boundary. Bounded old coordinates and the
existing inverse-fibre theorem select the correct old access. Thus the
incident-access and old-landing premises of TailActual are discharged.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketCoord Sec7.PocketJordan

variable {Ω : Type} [MeasurableSpace Ω]

/-- Construct R.5's rational old unfilled collar at the canonical current
landing, away from the terminal tip and the bounded pocket's outgoing corner.
No old incident access, transition limit or surviving point is an input. -/
theorem exists_rat_unfilled_collar_at_current_landing
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event)
    (hTrace : IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω))
    {a₀ T : ℝ} (ha₀ : 0 ≤ a₀) (haT : a₀ < T)
    (hVisit : d.curve ω T ∈ (j.target i d).domain ω) {ξ : ℝ}
    (hNotTip : j.currentVisitLanding i d ω T ξ ≠ d.curve ω T)
    (hNotExit : j.infinite = false → j.currentVisitLanding i d ω T ξ ≠
      cfPt (openPt (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed))) :
    ∃ s : ℚ, a₀ < (s : ℝ) ∧ (s : ℝ) < T ∧ ∃ x : ℝ, ∃ r > 0, ∃ ε > 0,
      Tendsto (fun z => (j.referenceVisitChart i d ω s).1
        ((j.referenceVisitChart i d ω T).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      Disjoint (d.curve ω '' Icc (s : ℝ) T)
        (closedBall (j.currentVisitLanding i d ω T ξ) r) ∧
      (j.referenceVisitChart i d ω s).2.1 '' (H ∩ ball (x : ℂ) ε) ⊆
        ball (j.currentVisitLanding i d ω T ξ) r ∧
      (j.referenceVisitChart i d ω s).2.1 '' (H ∩ ball (x : ℂ) ε) ⊆
        ((j.referenceVisitChart i d ω T).dom : Set ℂ) ∧
      Disjoint (ball (x : ℂ) ε)
        (currentPocketContacts (j.referenceVisitChart i d ω s) (j.referenceVisitChart i d ω T)) ∧
      Tendsto (j.referenceVisitChart i d ω s).2.1 (𝓝[H] (x : ℂ))
        (𝓝[(j.referenceVisitChart i d ω T).dom] (j.currentVisitLanding i d ω T ξ)) := by
  classical
  have hT : 0 ≤ T := ha₀.trans haT.le
  have hFrontier := currentVisitLanding_mem_current_frontier hj hRc hLc hω hT hVisit ξ
  rw [hTrace.2.2 T hT] at hFrontier
  obtain ⟨a, ha, ha₀a, haT', hAway⟩ := exists_old_interval_excluding_current_frontier
    hTrace.2.1 (isOpen_domain hj ω hω) (isDomainChart_baseChart hj hRc hLc hω).subset_H
    ha₀ haT hFrontier hNotTip
  have hNear : (d.curve ω) ⁻¹' (j.target i d).domain ω ∈ 𝓝 T :=
    (hTrace.2.1.continuousAt (Ici_mem_nhds (ha₀.trans_lt haT))).tendsto.eventually
      ((isOpen_domain hj ω hω).mem_nhds hVisit)
  obtain ⟨l, u, hTlu, hInterval⟩ := mem_nhds_iff_exists_Ioo_subset.1 hNear
  let b := max a l
  have hab : a ≤ b := le_max_left a l
  have hbT : b < T := max_lt haT' hTlu.1
  have hAccess (s : ℚ) (hbs : b < (s : ℝ)) (hsT : (s : ℝ) < T) :
      ∃ x : ℝ,
        Tendsto (fun z => (j.referenceVisitChart i d ω s).1
          ((j.referenceVisitChart i d ω T).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
        Tendsto (j.referenceVisitChart i d ω s).2.1 (𝓝[H] (x : ℂ))
          (𝓝 (j.currentVisitLanding i d ω T ξ)) := by
    have hVisitS : d.curve ω s ∈ (j.target i d).domain ω :=
      hInterval ⟨(le_max_right a l).trans_lt hbs, hsT.trans hTlu.2⟩
    refine exists_actual_old_incident_access hj hRc hLc hω hTrace
      (ha.trans (hab.trans hbs.le)) hsT.le hVisitS hVisit ?_ hNotExit
    change j.currentVisitLanding i d ω T ξ ∉
      ((j.referenceVisitChart i d ω s).dom : Set ℂ)
    rw [(isDomainChart_referenceVisitChart hj hRc hLc hω hTrace
      (ha.trans (hab.trans hbs.le)) hVisitS).coe_dom]
    exact hAway s (hab.trans_lt hbs)
  let x : ℚ → ℝ := fun s => if h : b < (s : ℝ) ∧ (s : ℝ) < T then
    (hAccess s h.1 h.2).choose else 0
  have hSpec (s : ℚ) (hbs : b < (s : ℝ)) (hsT : (s : ℝ) < T) :
      Tendsto (fun z => (j.referenceVisitChart i d ω s).1
        ((j.referenceVisitChart i d ω T).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x s : ℂ)) ∧
      Tendsto (j.referenceVisitChart i d ω s).2.1 (𝓝[H] (x s : ℂ))
        (𝓝 (j.currentVisitLanding i d ω T ξ)) := by
    dsimp only [x]
    rw [dite_eq_left ⟨hbs, hsT⟩]
    exact (hAccess s hbs hsT).choose_spec
  obtain ⟨s, hbs, hsT, r, hr, ε, hε, hTail, hBall, hCurrent, hContacts, hWithin⟩ :=
    exists_rat_actual_reference_unfilled_collar hj hRc hLc hω hTrace (ha.trans hab) hbT
      hVisit hNotTip (fun s hbs hsT => (hSpec s hbs hsT).2)
      (fun s hbs hsT => (hSpec s hbs hsT).1)
  exact ⟨s, (ha₀a.trans hab).trans_lt hbs, hsT, x s, r, hr, ε, hε,
    (hSpec s hbs hsT).1, hTail, hBall, hCurrent, hContacts, hWithin⟩

end InteractingSLE.Wire.Current.SideTest
