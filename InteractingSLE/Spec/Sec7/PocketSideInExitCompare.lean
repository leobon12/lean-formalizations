/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInExitOwn

/-!
# Excluding the inner outgoing corner on the entire current real boundary

PROVE-POCKET-SIDEIN. If the inner outgoing corner lies in the initial outer
pocket, its proved ambient survival puts it in the current outer interior.
If the two bounded outgoing corners agree, the outer inverse's own pole
exclusion applies. Both cases give exclusion at every real current access.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketStopField Sec7.PocketTraversal

variable {Ω : Type} [MeasurableSpace Ω]

/-- An inner outgoing corner in the initial outer interior remains in the
current outer interior at the common visit. Its unfilledness is proved. -/
theorem inner_outgoingSeed_mem_outer_current {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hInnerBounded : inner.infinite = false)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    (hInitialInterior : inner.outgoingSeed d ω ∈ (outer.target i d).domain ω) :
    inner.outgoingSeed d ω ∈ (relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω).dom := by
  change inner.outgoingSeed d ω ∈ ((relChart (outer.target i d).baseChart
    (outer.target i d).curve (outer.visitCapacity d ω t).toNNReal ω).dom : Set ℂ)
  rw [relChart_dom_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)]
  exact ⟨hInitialInterior, outgoingSeed_mem_active_at_original_visit hI hInnerBounded hωI ht hvisit⟩

/-- A current outer real access cannot land at the inner outgoing corner
when that corner is in the initial outer interior. -/
theorem currentVisitLanding_ne_inner_outgoing_of_initial_mem {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hInnerBounded : inner.infinite = false)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    (hInitialInterior : inner.outgoingSeed d ω ∈ (outer.target i d).domain ω) (x : ℝ) :
    outer.currentVisitLanding i d ω t x ≠ inner.outgoingSeed d ω := by
  have hc := (isDomainChart_relChart_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)).1
  have hnot := inverse_real_landing_notMem_dom hc
    (tendsto_currentVisitLanding hO hRc hLcO hωO ht (hUC hvisit) x)
  have hmem := inner_outgoingSeed_mem_outer_current hO hI hInnerBounded hRc hLcO
    hωO hωI hUC ht hvisit hInitialInterior
  intro heq
  rw [heq] at hnot
  exact hnot hmem

/-- The source outgoing-corner position replaces exclusion on every
current real access. No current boundary map or boundary coordinate is
part of the position hypothesis. -/
theorem currentVisitLanding_ne_inner_outgoing_of_exit_position {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    (hExitPosition : inner.infinite = false →
      inner.outgoingSeed d ω ∈ (outer.target i d).domain ω ∨
        (outer.infinite = false ∧ inner.outgoingSeed d ω = outer.outgoingSeed d ω)) :
    ∀ x : ℝ, inner.infinite = false →
      outer.currentVisitLanding i d ω t x ≠ inner.outgoingSeed d ω := by
  intro x hb
  rcases hExitPosition hb with hmem | ⟨hOuterBounded, heq⟩
  · exact currentVisitLanding_ne_inner_outgoing_of_initial_mem hO hI hb hRc hLcO
      hωO hωI hUC ht hvisit hmem x
  · rw [heq]
    exact currentVisitLanding_ne_outgoingSeed hO hOuterBounded hRc hLcO hωO ht (hUC hvisit) x

end InteractingSLE.Wire.Current.SideTest
