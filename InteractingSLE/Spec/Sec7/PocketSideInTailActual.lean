/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInTailContacts
import InteractingSLE.Spec.Sec7.PocketSideInSyncCharts

/-!
# Rational old collars for the actual native pocket charts

PROVE-POCKET-SIDEIN. Ready supplies each own-capacity chart and its domain
at an original visit. The ambient trace identifies its filled-hull cut.
The rational old reference is selected after these charts and their correct
incident accesses have been fixed. No nested-pocket visit is constructed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketTraversal Sec7.Lemma71C Sec7.PocketStop

variable {Ω : Type} [MeasurableSpace Ω]

/-- The existing current pocket chart, indexed by original ambient time. -/
def referenceVisitChart (j : SideTest Ω) (i : BothLow) (d : WordObjects Ω)
    (ω : Ω) (t : ℝ) : Chart :=
  relChart (j.target i d).baseChart (j.target i d).curve (j.visitCapacity d ω t).toNNReal ω

/-- The actual old chart has the literal physical trace-prefix domain. -/
theorem isDomainChart_referenceVisitChart {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event)
    (hTrace : IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω))
    {t : ℝ} (ht : 0 ≤ t) (hVisit : d.curve ω t ∈ (j.target i d).domain ω) :
    IsDomainChart ((j.target i d).domain ω ∩ (H \ fillH (d.curve ω '' Icc 0 t)))
      (j.referenceVisitChart i d ω t) := by
  have hc := isDomainChart_relChart_visitCapacity hj hRc hLc hω ht hVisit
  rwa [hTrace.2.2 t ht] at hc

/-- An actual side target's correct old incident accesses give a rational
reference with an unfilled collar, contact exclusion and the physical
current-domain approach. Both native shapes and both lifetime flags are covered. -/
theorem exists_rat_actual_reference_unfilled_collar
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event)
    (hTrace : IsLoewnerTrace (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω))
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (hVisit : d.curve ω T ∈ (j.target i d).domain ω)
    {p : ℂ} (hp : p ≠ d.curve ω T) {x : ℚ → ℝ} {ξ : ℝ}
    (hOldLanding : ∀ s : ℚ, a < (s : ℝ) → (s : ℝ) < T →
      Tendsto (j.referenceVisitChart i d ω s).2.1 (𝓝[H] (x s : ℂ)) (𝓝 p))
    (hIncidentTransition : ∀ s : ℚ, a < (s : ℝ) → (s : ℝ) < T →
      Tendsto (fun z => (j.referenceVisitChart i d ω s).1
        ((j.referenceVisitChart i d ω T).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x s : ℂ))) :
    ∃ s : ℚ, a < (s : ℝ) ∧ (s : ℝ) < T ∧ ∃ r > 0, ∃ ε > 0,
      Disjoint (d.curve ω '' Icc (s : ℝ) T) (closedBall p r) ∧
      (j.referenceVisitChart i d ω s).2.1 '' (H ∩ ball (x s : ℂ) ε) ⊆ ball p r ∧
      (j.referenceVisitChart i d ω s).2.1 '' (H ∩ ball (x s : ℂ) ε) ⊆
        ((j.referenceVisitChart i d ω T).dom : Set ℂ) ∧
      Disjoint (ball (x s : ℂ) ε)
        (currentPocketContacts (j.referenceVisitChart i d ω s) (j.referenceVisitChart i d ω T)) ∧
      Tendsto (j.referenceVisitChart i d ω s).2.1 (𝓝[H] (x s : ℂ))
        (𝓝[(j.referenceVisitChart i d ω T).dom] p) := by
  have hNow := isDomainChart_referenceVisitChart hj hRc hLc hω hTrace
    (ha.trans haT.le) hVisit
  have hNear : (d.curve ω) ⁻¹' (j.target i d).domain ω ∈ 𝓝 T :=
    (hTrace.2.1.continuousAt (Ici_mem_nhds (ha.trans_lt haT))).tendsto.eventually
      ((isOpen_domain hj ω hω).mem_nhds hVisit)
  obtain ⟨l, u, hTlu, hInterval⟩ := mem_nhds_iff_exists_Ioo_subset.1 hNear
  let b := max a l
  have hbT : b < T := max_lt haT hTlu.1
  have hab : a ≤ b := le_max_left a l
  have hOldVisits (s : ℚ) (hbs : b < (s : ℝ)) (hsT : (s : ℝ) < T) :
      d.curve ω s ∈ (j.target i d).domain ω :=
    hInterval ⟨(le_max_right a l).trans_lt hbs, hsT.trans hTlu.2⟩
  have hOld (s : ℚ) (has : b < (s : ℝ)) (hsT : (s : ℝ) < T) :=
    isDomainChart_referenceVisitChart hj hRc hLc hω hTrace
      (ha.trans (hab.trans has.le)) (hOldVisits s has hsT)
  have hReference (s : ℚ) (has : b < (s : ℝ)) (hsT : (s : ℝ) < T) :
      (j.referenceVisitChart i d ω s).IsConformal ∧
        (j.referenceVisitChart i d ω s).dom =
          (j.target i d).domain ω ∩ (H \ fillH (d.curve ω '' Icc 0 (s : ℝ))) :=
    ⟨(hOld s has hsT).1, (hOld s has hsT).coe_dom⟩
  have hIncident (s : ℚ) (has : b < (s : ℝ)) (hsT : (s : ℝ) < T) :
      (x s : ℂ) ∈ closure ((j.referenceVisitChart i d ω s).1 ''
        ((j.target i d).domain ω ∩ (H \ fillH (d.curve ω '' Icc 0 T)))) := by
    rw [← hNow.coe_dom]
    exact old_access_mem_closure_of_current_transition hNow.1 (hIncidentTransition s (hab.trans_lt has) hsT)
  obtain ⟨s, has, hsT, r, hr, ε, hε, hTail, hBall, hCurrent, -⟩ :=
    exists_rat_reference_unfilled_collar hTrace.2.1 (ha.trans hab) hbT hp hReference
      (fun s has hsT => hOldLanding s (hab.trans_lt has) hsT) hIncident
  have hCurrent' : (j.referenceVisitChart i d ω s).2.1 '' (H ∩ ball (x s : ℂ) ε) ⊆
      ((j.referenceVisitChart i d ω T).dom : Set ℂ) := by
    rwa [hNow.coe_dom]
  have hInclusion : ((j.referenceVisitChart i d ω T).dom : Set ℂ) ⊆
      (j.referenceVisitChart i d ω s).dom := by
    rw [hNow.coe_dom, (hOld s has hsT).coe_dom]
    exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2
      (fillH_mono (image_mono (Icc_subset_Icc_right hsT.le)) h)⟩
  have hCollar := halfDisc_subset_transition_of_inverse_image
    (hOld s has hsT).1 hNow.1 hInclusion hCurrent'
  exact ⟨s, hab.trans_lt has, hsT, r, hr, ε, hε, hTail, hBall, hCurrent',
    disjoint_currentPocketContacts_of_halfDisc (hOld s has hsT).1 hNow.1 hInclusion hCollar,
    tendsto_old_inverse_within_current_of_halfDisc (hOldLanding s (hab.trans_lt has) hsT) hε hCurrent'⟩

end InteractingSLE.Wire.Current.SideTest
