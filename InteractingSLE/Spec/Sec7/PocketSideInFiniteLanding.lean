/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInFiniteCurrent

/-!
# Canonical physical landings at the actual common visit

PROVE-POCKET-SIDEIN. Construct the current inverse's boundary extension
from the already proved initial Jordan and finite-prefix extensions.
On a shared collar its physical landing belongs to the initial inner
pocket's closure. Only exclusion of the inner outgoing corner remains.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketStopSide
  Sec7.PocketStop Sec7.PocketTraversal Sec7.PocketStopField Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω]

/-- The actual current inverse's canonical finite boundary extension. -/
def currentVisitLanding (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω) (ω : Ω) (t : ℝ) : ℂ → ℂ :=
  extendFrom H (relChart (j.target i d).baseChart (j.target i d).curve
    (j.visitCapacity d ω t).toNNReal ω).2.1

/-- Both initial pocket shapes and the actual own prefix supply the
continuous current inverse extension, with physical values in the initial
pocket's closure. -/
theorem currentVisitLanding_spec {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) :
    EqOn (j.currentVisitLanding i d ω t)
      (relChart (j.target i d).baseChart (j.target i d).curve
        (j.visitCapacity d ω t).toNNReal ω).2.1 H ∧
    ContinuousOn (j.currentVisitLanding i d ω t) Hbar ∧
    MapsTo (j.currentVisitLanding i d ω t) Hbar (closure ((j.target i d).domain ω)) := by
  have hc := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  obtain ⟨E, hE, hEc, hED⟩ := exists_inverse_extension_of_jordan_cases
    (jordan_cases hj ω hω) hc.1 hc.2.1 hc.2.2.1
  obtain ⟨F, hF, hFc, hFD⟩ := exists_relative_inverse_extension
    (c := (j.target i d).baseChart) (isDrivenCurve_target hj ω hω)
    (visitCapacity_spec hj hω ht hvisit).2.1 hE hEc
  have heq : EqOn (j.currentVisitLanding i d ω t) F Hbar := by
    intro z hz
    have hzcl : z ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact hz
    apply extendFrom_eq hzcl
    exact (((hFc z hz).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hw => hF hw)
  refine ⟨?_, hFc.congr (fun _ hz => heq hz), ?_⟩
  · exact extendFrom_extends
      (isDomainChart_relChart_visitCapacity hj hRc hLc hω ht hvisit).1.1.continuousOn
  · intro z hz
    rw [heq hz]
    obtain ⟨y, hy, hFy⟩ := hFD hz
    exact hFy ▸ hED hy

/-- The actual physical landing, with the approach from the entire upper
half-plane. This can instantiate the incoming-germ landing premise. -/
theorem tendsto_currentVisitLanding {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) (x : ℝ) :
    Tendsto (relChart (j.target i d).baseChart (j.target i d).curve
      (j.visitCapacity d ω t).toNNReal ω).2.1 (𝓝[H] (x : ℂ))
      (𝓝 (j.currentVisitLanding i d ω t x)) := by
  obtain ⟨heq, hc, -⟩ := currentVisitLanding_spec hj hRc hLc hω ht hvisit
  exact (((hc _ (mem_Hbar_of_im_eq_zero (by simp))).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
    (eventually_nhdsWithin_of_forall fun _ hz => heq hz)

/-- A shared current half-disc forces the canonical outer physical landing
into the initial inner pocket's closure. No separate landing-location
hypothesis is required. -/
theorem currentVisitLanding_mem_closure_inner {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω)
    {x r : ℝ} (hr : 0 < r)
    (hCollar :
      let O := relChart (outer.target i d).baseChart (outer.target i d).curve
        (outer.visitCapacity d ω t).toNNReal ω
      let I := relChart (inner.target i d).baseChart (inner.target i d).curve
        (inner.visitCapacity d ω t).toNNReal ω
      H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart O I).dom : Set ℂ)) :
    outer.currentVisitLanding i d ω t x ∈ closure ((inner.target i d).domain ω) := by
  have ho := (isDomainChart_relChart_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)).1
  have hi := (isDomainChart_relChart_visitCapacity hI hRc hLcI hωI ht hvisit).1
  have hincl := current_domain_inclusion_at_visit hO hI hRc hLcO hLcI hωO hωI hUC ht hvisit
  have hlim := tendsto_currentVisitLanding hO hRc hLcO hωO ht (hUC hvisit) x
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hr)] with z hz hzball
  have hmem := (mem_dom_pocketTransitionChart ho hi hincl).1 (hCollar ⟨hz, hzball⟩)
  have hdom := relChart_dom_visitCapacity hI hRc hLcI hωI ht hvisit
  have hp : _ ∈ ((relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω).dom : Set ℂ) := hmem.2
  rw [hdom] at hp
  exact subset_closure hp.1

end InteractingSLE.Wire.Current.SideTest
