/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainTopology
import InteractingSLE.Spec.Sec7.PocketSideInExitGerm

/-!
# R.5 germs for independently normalized fixed candidates

PROVE-POCKET-SIDEIN. Each candidate is normalized on its own event.
The marked comparison is proved on one event before selecting the physical
point, chart, shared collar or realized nested witness.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketUnionPt

open Classical in
/-- Normalize the initial active pocket on its own candidate event. -/
def eventDomain {Ω : Type*} (M : Set Ω) (C : Ω → Set ℂ) (ω : Ω) : Set ℂ :=
  if ω ∈ M then C ω else ∅

/-- The fixed original-time filled record is exactly the complement filling
of the independently normalized initial domain. -/
theorem extHullSet_eventDomain {Ω : Type*} (M : Set Ω) (C F : Ω → Set ℂ) :
    (fun ω => extHullSet (eventDomain M C ω) (F ω)) = eventFilled M C F := by
  funext ω
  by_cases hω : ω ∈ M
  · simp only [eventDomain, eventFilled, hω, ↓reduceIte]
  · simp only [eventDomain, eventFilled, hω, ↓reduceIte, extHullSet,
      compl_empty, univ_union, inter_univ]

/-- The filled-law comparison applies to physical current domains on both
candidate events, with no off-event geometry and no boundary-membership input. -/
theorem ae_germ_of_separate_candidate_laws {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {MO MU : Set Ω} {C U F : Ω → Set ℂ}
    (hCm : Measurable[mΩ, hittingSigma] (eventFilled MO C F))
    (hUm : Measurable[mΩ, hittingSigma] (eventFilled MU U F))
    (hCloc : IsLocalSet (eventFilled MO C F) h P)
    (hUloc : IsLocalSet (eventFilled MU U F) h P)
    (hPair : IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (eventFilled MO C F) hittingSigma ⊔
        MeasurableSpace.comap (eventFilled MU U F) hittingSigma)
      (fun ω => eventFilled MO C F ω ∪ eventFilled MU U F ω) h P)
    (hCunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (eventFilled MO C F ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (eventFilled MO C F ω)) z))
    (hUunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (eventFilled MU U F ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (eventFilled MU U F ω)) z))
    {gC gU : Ω → DistOn upperHalfPlaneOpens}
    (hgC : IsLocalSetMean (eventFilled MO C F) h P gC)
    (hgU : IsLocalSetMean (eventFilled MU U F) h P gU) :
    ∀ᵐ ω ∂P, ω ∈ MO → ω ∈ MU → ∀ vC vU : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vC (H \ eventFilled MO C F ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ eventFilled MO C F ω →
        gC ω φ = ∫ z, vC z * φ z) →
      InnerProductSpace.HarmonicOnNhd vU (H \ eventFilled MU U F ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ eventFilled MU U F ω →
        gU ω φ = ∫ z, vU z * φ z) → ∀ outer inner : Chart,
      outer.IsConformal → inner.IsConformal → (inner.dom : Set ℂ) ⊆ outer.dom →
      (outer.dom : Set ℂ) = C ω ∩ (H \ F ω) →
      (inner.dom : Set ℂ) = U ω ∩ (H \ F ω) → ∀ (p : ℂ) (ξ r : ℝ),
      (∃ ε > 0, C ω ∩ ball p ε = U ω ∩ ball p ε) → 0 < r →
      H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ) →
      Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
      Tendsto (fun z => vU (outer.2.1 z) - vC (outer.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have heC (ω : Ω) : extHullSet (eventDomain MO C ω) (F ω) = eventFilled MO C F ω :=
    congrFun (extHullSet_eventDomain MO C F) ω
  have heU (ω : Ω) : extHullSet (eventDomain MU U ω) (F ω) = eventFilled MU U F ω :=
    congrFun (extHullSet_eventDomain MU U F) ω
  have hGood : ∀ᵐ ω ∂P, _ :=
    ae_current_germ_of_shared_neighborhood_and_landing hh
      (C := eventDomain MO C) (U := eventDomain MU U) (F := F)
      (by simpa only [extHullSet_eventDomain] using hCm)
      (by simpa only [extHullSet_eventDomain] using hUm)
      (by simpa only [extHullSet_eventDomain] using hCloc)
      (by simpa only [extHullSet_eventDomain] using hUloc)
      (by simpa only [extHullSet_eventDomain, heC, heU] using hPair)
      (by simpa only [heC] using hCunb)
      (by simpa only [heU] using hUunb)
      (by simpa only [extHullSet_eventDomain] using hgC)
      (by simpa only [extHullSet_eventDomain] using hgU)
  filter_upwards [hGood] with ω hω hO hU
  simpa only [eventDomain, eventFilled, hO, hU, ↓reduceIte] using hω

end InteractingSLE.Sec7.PocketStopSide
