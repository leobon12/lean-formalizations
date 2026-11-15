/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInExitExtension
import InteractingSLE.Spec.Sec7.PocketSideInLogTransition

/-!
# Actual inherited transition logarithms from ready domain charts

PROVE-POCKET-SIDEIN. The actual current domain charts already carry their
analytic lifts. Extracting these lifts and extending their chain-rule
difference constructs the boundary logarithm without a separate log input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (schwarzReflect)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

/-- Domain-chart data supplies the inherited analytic transition log.
Its boundary extension retains the current lift without an independent
integer or branch choice. -/
theorem exists_inherited_transition_log_of_domain_charts {outer inner : Chart} {C U : Set ℂ}
    (hO : IsDomainChart C outer) (hI : IsDomainChart U inner)
    (hIncl : (inner.dom : Set ℂ) ⊆ outer.dom) {G : ℂ → ℂ}
    (hEq : EqOn G (pocketTransitionChart outer inner).1 (pocketTransitionChart outer inner).dom)
    {J : Set ℝ} (hJo : IsOpen J)
    (hCollars : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart outer inner).dom : Set ℂ))
    (hReflect : ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r) :
    ∃ Lbar : ℂ → ℂ,
      IsDerivLog (pocketTransitionChart outer inner).1 Lbar (pocketTransitionChart outer inner).dom ∧
      (∀ z ∈ (pocketTransitionChart outer inner).dom,
        (Lbar z).im = (pocketTransitionChart outer inner).2.2 z) ∧
      ContinuousOn Lbar (((pocketTransitionChart outer inner).dom : Set ℂ) ∪ ofReal '' J) ∧
      (∀ x ∈ J, ContinuousWithinAt Lbar Hbar (x : ℂ)) ∧
      (∀ x ∈ J, exp (Lbar x) = deriv (schwarzReflect G) x) := by
  have hOuterLogs := hO.2.2
  have hInnerLogs := hI.2.2
  rw [← hO.coe_dom] at hOuterLogs
  rw [← hI.coe_dom] at hInnerLogs
  obtain ⟨LO, hLO, hLiftO⟩ := hOuterLogs
  obtain ⟨LI, hLI, hLiftI⟩ := hInnerLogs
  have hLog := isDerivLog_pocketTransitionLog hO.1 hI.1 hIncl hLO hLI
  obtain ⟨Lbar, hLbar, hLc, hLwithin, hExp⟩ := exists_inherited_log_extension
    (isConformal_pocketTransitionChart hO.1 hI.1 hIncl) hLog hEq hJo hCollars hReflect
  refine ⟨Lbar, ⟨hLog.1.congr (fun _ hz => hLbar hz), ?_⟩, ?_, hLc, hLwithin, hExp⟩
  · intro z hz
    rw [hLbar hz]
    exact hLog.2 z hz
  · intro z hz
    rw [hLbar hz]
    exact im_pocketTransitionLog hO.1 hI.1 hIncl (fun _ hp => hLiftO hp)
      (fun _ hp => hLiftI hp) z hz

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketStopField Sec7.PocketTraversal
open Theorem14.GB11Chart
open WangWu (negInv)

variable {Ω : Type} [MeasurableSpace Ω]

/-- The actual current transition has a reflected extension and a boundary
logarithm carrying its exact inherited lift. The remaining geometry is
the actual gate, the shared collars and the initial outgoing-corner relation. -/
theorem exists_transition_log_of_exit_position {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hOuterOwn : relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω =
        ((outer.target i d).baseChart ω).loewner W (outer.visitCapacity d ω t).toNNReal)
    (b : CurrentGateBoundary W
      (negInv '' (((outer.target i d).baseChart ω).1 '' (inner.target i d).domain ω))
      (outer.visitCapacity d ω t).toNNReal)
    {J : Set ℝ} (hJo : IsOpen J)
    (hCollars :
      let O := relChart (outer.target i d).baseChart (outer.target i d).curve
        (outer.visitCapacity d ω t).toNNReal ω
      let I := relChart (inner.target i d).baseChart (inner.target i d).curve
        (inner.visitCapacity d ω t).toNNReal ω
      ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart O I).dom : Set ℂ))
    (hExitPosition : inner.infinite = false →
      inner.outgoingSeed d ω ∈ (outer.target i d).domain ω ∨
        (outer.infinite = false ∧ inner.outgoingSeed d ω = outer.outgoingSeed d ω)) :
    let O := relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω
    let I := relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω
    let T := pocketTransitionChart O I
    ∃ G Lbar : ℂ → ℂ, EqOn G T.1 T.dom ∧
      ContinuousOn G ((T.dom : Set ℂ) ∪ ofReal '' J) ∧
      (∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r) ∧
      IsDerivLog T.1 Lbar T.dom ∧
      (∀ z ∈ T.dom, (Lbar z).im = T.2.2 z) ∧
      ContinuousOn Lbar ((T.dom : Set ℂ) ∪ ofReal '' J) ∧
      (∀ x ∈ J, ContinuousWithinAt Lbar Hbar (x : ℂ)) ∧
      (∀ x ∈ J, exp (Lbar x) = deriv (schwarzReflect G) x) := by
  obtain ⟨G, hG, hGc, hReflect⟩ := exists_transition_extension_of_exit_position hO hI hRc hLcO hLcI
    hωO hωI hUC ht hvisit hW hW0 hOuterOwn b hJo hCollars hExitPosition
  have ho := isDomainChart_relChart_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)
  have hi := isDomainChart_relChart_visitCapacity hI hRc hLcI hωI ht hvisit
  have hIncl := current_domain_inclusion_at_visit hO hI hRc hLcO hLcI hωO hωI hUC ht hvisit
  obtain ⟨Lbar, hLog, hLift, hLc, hWithin, hExp⟩ :=
    exists_inherited_transition_log_of_domain_charts ho hi hIncl hG hJo hCollars hReflect
  exact ⟨G, Lbar, hG, hGc, hReflect, hLog, hLift, hLc, hWithin, hExp⟩

end InteractingSLE.Wire.Current.SideTest
