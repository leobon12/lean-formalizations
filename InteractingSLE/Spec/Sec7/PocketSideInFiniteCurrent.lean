/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFiniteInitial
import InteractingSLE.Spec.Sec7.PocketSideInFiniteGate

/-!
# Finite extensions for the actual common-visit pocket transition

PROVE-POCKET-SIDEIN. Both current charts use the constructed original-visit
capacities. Ready supplies the initial finite chart at a physical landing
away from the inner outgoing corner. The actual face identification remains
a named geometric input; no new stopped-field law is asserted here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketStopSide
  Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketStopField Sec7.Lemma71C
open Theorem14.GB11Chart

variable {Ω : Type} [MeasurableSpace Ω]

/-- A physical landing in the finite part of the actual initial inner chart
bounds the actual current transition at that access. The landing may lie
on the exposed counterflow, and its own Loewner image need not survive. -/
theorem local_bound_current_transition_at_original_visit {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    {x : ℝ} {p : ℂ} (hp : p ∈ closure ((inner.target i d).domain ω))
    (hNotExit : inner.infinite = false →
      p ≠ cfPt (openPt (d.rightWall ω) (d.leftWall inner.seed ω) (StripSys.rt inner.seed)))
    (hLanding : Tendsto (relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω).2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) :
    let O := relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω
    let I := relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω
    ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart O I).1 z‖ ≤ M := by
  let O := relChart (outer.target i d).baseChart (outer.target i d).curve
    (outer.visitCapacity d ω t).toNNReal ω
  let I := relChart (inner.target i d).baseChart (inner.target i d).curve
    (inner.visitCapacity d ω t).toNNReal ω
  change ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ),
    ‖(pocketTransitionChart O I).1 z‖ ≤ M
  have ho := (isDomainChart_relChart_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)).1
  have hb := (isDomainChart_baseChart hI hRc hLcI hωI).1
  have hi := current_domain_inclusion_at_visit hO hI hRc hLcO hLcI hωO hωI hUC ht hvisit
  change (I.dom : Set ℂ) ⊆ O.dom at hi
  obtain ⟨W, hW, hW0, _, _, _, heq⟩ := exists_relChart_eq_loewner
    (c := (inner.target i d).baseChart) (isDrivenCurve_target hI ω hωI)
    (visitCapacity_spec hI hωI ht hvisit).2.1
  change I = ((inner.target i d).baseChart ω).loewner W _ at heq
  obtain ⟨E, hE, hEc⟩ := exists_initial_finite_extension_of_ready hI hRc hLcI hωI hp hNotExit
  rw [heq] at hi ⊢
  apply eventually_norm_bounded_current_transition_of_landing ho hb hW hW0
    (inner.visitCapacity d ω t).toNNReal.coe_nonneg hi _ hE hEc
  exact hLanding.mono_left (nhdsWithin_mono _
    (isConformal_pocketTransitionChart ho (hb.loewner hW hW0
      (inner.visitCapacity d ω t).toNNReal.coe_nonneg) hi).dom_subset)

/-- The finite extension and local positive reflection for the actual
common-visit transition. The remaining geometry identifies its current
domain with the constructed gate face and locates its finite physical
landings; all map extensions and local bounds are conclusions. -/
theorem exists_transition_extension_at_original_visit {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    {W : ℝ → ℝ} {C : Set ℂ} {s : ℝ} (b : CurrentGateBoundary W C s)
    {J : Set ℝ} (hJo : IsOpen J)
    (hFaceDomain :
      let O := relChart (outer.target i d).baseChart (outer.target i d).curve
        (outer.visitCapacity d ω t).toNNReal ω
      let I := relChart (inner.target i d).baseChart (inner.target i d).curve
        (inner.visitCapacity d ω t).toNNReal ω
      ((pocketTransitionChart O I).dom : Set ℂ) = ownDomain W C s)
    (hCollars :
      let O := relChart (outer.target i d).baseChart (outer.target i d).curve
        (outer.visitCapacity d ω t).toNNReal ω
      let I := relChart (inner.target i d).baseChart (inner.target i d).curve
        (inner.visitCapacity d ω t).toNNReal ω
      ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart O I).dom : Set ℂ))
    (hFiniteLandings : ∀ x ∈ J, ∃ p ∈ closure ((inner.target i d).domain ω),
      (inner.infinite = false →
        p ≠ cfPt (openPt (d.rightWall ω) (d.leftWall inner.seed ω) (StripSys.rt inner.seed))) ∧
      Tendsto (relChart (outer.target i d).baseChart (outer.target i d).curve
        (outer.visitCapacity d ω t).toNNReal ω).2.1 (𝓝[H] (x : ℂ)) (𝓝 p)) :
    let O := relChart (outer.target i d).baseChart (outer.target i d).curve
      (outer.visitCapacity d ω t).toNNReal ω
    let I := relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω
    ∃ G : ℂ → ℂ, EqOn G (pocketTransitionChart O I).1 (pocketTransitionChart O I).dom ∧
      ContinuousOn G (((pocketTransitionChart O I).dom : Set ℂ) ∪ Complex.ofReal '' J) ∧
      ∀ x ∈ J, ∃ r > 0, R16.IsRealBoundaryConformal G x r := by
  have ho := (isDomainChart_relChart_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)).1
  have hi := (isDomainChart_relChart_visitCapacity hI hRc hLcI hωI ht hvisit).1
  have hincl := current_domain_inclusion_at_visit hO hI hRc hLcO hLcI hωO hωI hUC ht hvisit
  apply exists_shared_extension_of_current_face_bound b
    (isConformal_pocketTransitionChart ho hi hincl) hFaceDomain hJo hCollars
  intro x hx
  obtain ⟨p, hp, hne, hland⟩ := hFiniteLandings x hx
  exact local_bound_current_transition_at_original_visit hO hI hRc hLcO hLcI
    hωO hωI hUC ht hvisit hp hne hland

end InteractingSLE.Wire.Current.SideTest
