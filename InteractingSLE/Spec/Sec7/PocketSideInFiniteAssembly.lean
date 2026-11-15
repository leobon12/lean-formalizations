/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFiniteFace

/-!
# Actual-pocket finite extension from the remaining gate geometry

PROVE-POCKET-SIDEIN. The inputs are the actual nested gate boundary, shared
collars, and exclusion of the inner outgoing corner on their canonical
physical landings. The current-domain identity, all finite landings,
initial extensions, local bounds, current extension and reflection are proved.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketStopSide
  Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketStopField
open Theorem14.GB11Chart
open WangWu (negInv)

variable {Ω : Type} [MeasurableSpace Ω]

/-- R.6's finite transition extension for actual pockets. The gate is for
the specified initial inner domain in the initial outer chart, at the
actual outer visit capacity. Its identity with the current transition
domain is a conclusion of the common-hull calculation, not an input. -/
theorem exists_transition_extension_of_actual_gate {outer inner : SideTest Ω} {i : BothLow}
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
    (hNotExit : ∀ x ∈ J, inner.infinite = false →
      outer.currentVisitLanding i d ω t x ≠
        cfPt (openPt (d.rightWall ω) (d.leftWall inner.seed ω) (StripSys.rt inner.seed))) :
    let O := relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω
    let I := relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω
    ∃ G : ℂ → ℂ, EqOn G (pocketTransitionChart O I).1 (pocketTransitionChart O I).dom ∧
      ContinuousOn G (((pocketTransitionChart O I).dom : Set ℂ) ∪ Complex.ofReal '' J) ∧
      ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r := by
  apply exists_transition_extension_at_original_visit hO hI hRc hLcO hLcI
    hωO hωI hUC ht hvisit b hJo
    (transition_domain_eq_ownDomain_at_original_visit hO hI hRc hLcO hLcI
      hωO hωI hUC ht hvisit hW hW0 hOuterOwn) hCollars
  intro x hx
  obtain ⟨r, hr, hcol⟩ := hCollars x hx
  exact ⟨outer.currentVisitLanding i d ω t x,
    currentVisitLanding_mem_closure_inner hO hI hRc hLcO hLcI hωO hωI hUC ht hvisit hr hcol,
    hNotExit x hx, tendsto_currentVisitLanding hO hRc hLcO hωO ht (hUC hvisit) x⟩

end InteractingSLE.Wire.Current.SideTest
