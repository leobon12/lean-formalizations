/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInExitCompare

/-!
# Actual-pocket extension from the initial outgoing-corner position

PROVE-POCKET-SIDEIN. The remaining corner input is a relation between the
initial physical pockets. Exclusion on the full current real interval is
proved using outgoing survival or the common outgoing pole.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketStopField Sec7.PocketTraversal
open Theorem14.GB11Chart
open WangWu (negInv)

variable {Ω : Type} [MeasurableSpace Ω]

/-- The actual finite current transition extension, with current corner
exclusion replaced by the specified initial outgoing-corner position. -/
theorem exists_transition_extension_of_exit_position {outer inner : SideTest Ω} {i : BothLow}
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
    ∃ G : ℂ → ℂ, EqOn G (pocketTransitionChart O I).1 (pocketTransitionChart O I).dom ∧
      ContinuousOn G (((pocketTransitionChart O I).dom : Set ℂ) ∪ Complex.ofReal '' J) ∧
      ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r := by
  apply exists_transition_extension_of_actual_gate hO hI hRc hLcO hLcI
    hωO hωI hUC ht hvisit hW hW0 hOuterOwn b hJo hCollars
  intro x _ hb
  exact currentVisitLanding_ne_inner_outgoing_of_exit_position hO hI hRc hLcO
    hωO hωI hUC ht hvisit hExitPosition x hb

end InteractingSLE.Wire.Current.SideTest
