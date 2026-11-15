/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInPatchTip

/-!
# Actual current collars around the centered driver

PROVE-POCKET-SIDEIN. At a common interior visit the outer current inverse
lands at the actual tip, inside the initial inner pocket. Continuity gives
an interval of such landings. The common ambient hull then supplies a
current transition collar at every point in that interval.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop

variable {Ω : Type} [MeasurableSpace Ω]

/-- Every actual outer current access landing in the open initial inner
pocket has a current transition collar. -/
theorem current_collar_at_inner_landing {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    {ξ : ℝ} (hp : outer.currentVisitLanding i d ω t ξ ∈ (inner.target i d).domain ω) :
    let O := relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω
    let I := relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω
    ∃ r > 0, H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart O I).dom : Set ℂ) := by
  exact current_collar_of_landing_mem_inner
    (isDomainChart_relChart_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)).1
    (isDomainChart_relChart_visitCapacity hI hRc hLcI hωI ht hvisit).1
    (isOpen_domain hI ω hωI) hUC
    (relChart_dom_visitCapacity hO hRc hLcO hωO ht (hUC hvisit))
    (relChart_dom_visitCapacity hI hRc hLcI hωI ht hvisit) hp
    (tendsto_currentVisitLanding hO hRc hLcO hωO ht (hUC hvisit) ξ)

/-- A common interior visit gives an open real interval around zero whose
outer current accesses all land in the initial inner pocket. -/
theorem exists_driver_interval_landings_inner {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω) :
    ∃ ε > 0, ∀ ξ : ℝ, |ξ| < ε →
      outer.currentVisitLanding i d ω t ξ ∈ (inner.target i d).domain ω := by
  have hCont : Continuous (fun ξ : ℝ => outer.currentVisitLanding i d ω t ξ) :=
    (currentVisitLanding_spec hO hRc hLcO hωO ht (hUC hvisit)).2.1.comp_continuous
      Complex.continuous_ofReal (fun _ => mem_Hbar_of_im_eq_zero (by simp))
  have hZero : outer.currentVisitLanding i d ω t (0 : ℂ) ∈ (inner.target i d).domain ω := by
    rw [currentVisitLanding_zero hO hRc hLcO hωO ht (hUC hvisit)]
    exact hvisit
  have hOpen := (isOpen_domain hI ω hωI).preimage hCont
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.1 hOpen 0 hZero
  refine ⟨ε, hε, fun ξ hξ => hBall ?_⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hξ

/-- At the common actual visit, a whole driver interval has shared current
collars, without a surviving initial coordinate or a supplied collar. -/
theorem exists_driver_interval_collars {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω) :
    let O := relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω
    let I := relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω
    ∃ ε > 0, ∀ ξ : ℝ, |ξ| < ε →
      outer.currentVisitLanding i d ω t ξ ∈ (inner.target i d).domain ω ∧
      ∃ r > 0, H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart O I).dom : Set ℂ) := by
  obtain ⟨ε, hε, hLanding⟩ := exists_driver_interval_landings_inner
    hO hI hRc hLcO hωO hωI hUC ht hvisit
  exact ⟨ε, hε, fun ξ hξ => ⟨hLanding ξ hξ, current_collar_at_inner_landing
    hO hI hRc hLcO hLcI hωO hωI hUC ht hvisit (hLanding ξ hξ)⟩⟩

end InteractingSLE.Wire.Current.SideTest
