/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRealCurrent

/-!
# The incoming physical germ from a shared pocket neighborhood

PROVE-POCKET-SIDEIN. This comparison also covers an unvisited incoming
frontier point, outside the ambient hull. Local agreement of the two actual
initial pockets gives local agreement of their current filled sets. A
shared current half-disc puts the inverse approach in their common
complement. The joint marked law remains an explicit source-law input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketUnionPt

/-- The same ambient cut preserves local equality of the initial pockets. -/
theorem extHullSet_inter_ball_eq_of_pocket_agreement {C U F : Set ℂ} {p : ℂ} {r : ℝ}
    (hLocal : C ∩ ball p r = U ∩ ball p r) :
    extHullSet C F ∩ ball p r = extHullSet U F ∩ ball p r := by
  ext z
  constructor
  · rintro ⟨⟨hzH, hzC | hzF⟩, hzball⟩
    · refine ⟨⟨hzH, Or.inl fun hzU => ?_⟩, hzball⟩
      exact hzC (show z ∈ C from (hLocal.symm ▸ (show z ∈ U ∩ ball p r from ⟨hzU, hzball⟩)).1)
    · exact ⟨⟨hzH, Or.inr hzF⟩, hzball⟩
  · rintro ⟨⟨hzH, hzU | hzF⟩, hzball⟩
    · refine ⟨⟨hzH, Or.inl fun hzC => ?_⟩, hzball⟩
      exact hzU (show z ∈ U from (hLocal ▸ (show z ∈ C ∩ ball p r from ⟨hzC, hzball⟩)).1)
    · exact ⟨⟨hzH, Or.inr hzF⟩, hzball⟩

/-- A shared half-disc and the common original-hull identities put the
outer inverse approach in the complement of both current filled sets. -/
theorem tendsto_inverse_common_complement {outer inner : Chart}
    (hO : outer.IsConformal) (hI : inner.IsConformal)
    (hCurrentInclusion : (inner.dom : Set ℂ) ⊆ outer.dom) {C U F : Set ℂ}
    (hOuterCurrent : (outer.dom : Set ℂ) = C ∩ (H \ F))
    (hInnerCurrent : (inner.dom : Set ℂ) = U ∩ (H \ F))
    {ξ r : ℝ} (hr : 0 < r)
    (hCollar : H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ))
    {p : ℂ} (hLanding : Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p)) :
    Tendsto outer.2.1 (𝓝[H] (ξ : ℂ))
      (𝓝[H \ (extHullSet C F ∪ extHullSet U F)] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨hLanding, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (ball_mem_nhds (ξ : ℂ) hr)] with z hzH hzball
  have hpI := (mem_dom_pocketTransitionChart hO hI hCurrentInclusion).1 (hCollar ⟨hzH, hzball⟩) |>.2
  have hpO := hCurrentInclusion hpI
  rw [hOuterCurrent] at hpO
  change outer.2.1 z ∈ (inner.dom : Set ℂ) at hpI
  rw [hInnerCurrent] at hpI
  refine ⟨hpO.2.1, fun h => ?_⟩
  rcases h with hC | hU
  · exact hC.2.elim (fun hnot => hnot hpO.1) hpO.2.2
  · exact hU.2.elim (fun hnot => hnot hpI.1) hpI.2.2

/-- A shared initial pocket neighborhood gives the physical R.5 germ at a
current shared side, including an unvisited frontier point. The one event
is uniform over all harmonic representatives, charts, landings and collars.
The law is for the fixed candidate pair and original hull supplied as C,U,F;
it is not evaluated at a future-selected relative stopping time. -/
theorem ae_current_germ_of_shared_pocket_neighborhood {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {C U F : Ω → Set ℂ}
    (hCm : Measurable[mΩ, hittingSigma] (fun ω => extHullSet (C ω) (F ω)))
    (hUm : Measurable[mΩ, hittingSigma] (fun ω => extHullSet (U ω) (F ω)))
    (hCloc : IsLocalSet (fun ω => extHullSet (C ω) (F ω)) h P)
    (hUloc : IsLocalSet (fun ω => extHullSet (U ω) (F ω)) h P)
    (hPairMarked : WholeField.IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (fun ω => extHullSet (C ω) (F ω)) hittingSigma ⊔
        MeasurableSpace.comap (fun ω => extHullSet (U ω) (F ω)) hittingSigma)
      (fun ω => extHullSet (C ω) (F ω) ∪ extHullSet (U ω) (F ω)) h P)
    (hCunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (extHullSet (C ω) (F ω)),
      ¬ IsBounded (connectedComponentIn (lowerUnion (extHullSet (C ω) (F ω))) z))
    (hUunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (extHullSet (U ω) (F ω)),
      ¬ IsBounded (connectedComponentIn (lowerUnion (extHullSet (U ω) (F ω))) z))
    {gC gU : Ω → DistOn upperHalfPlaneOpens}
    (hgC : IsLocalSetMean (fun ω => extHullSet (C ω) (F ω)) h P gC)
    (hgU : IsLocalSetMean (fun ω => extHullSet (U ω) (F ω)) h P gU) :
    ∀ᵐ ω ∂P, ∀ vC vU : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vC (H \ extHullSet (C ω) (F ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ extHullSet (C ω) (F ω) →
        gC ω φ = ∫ z, vC z * φ z) →
      InnerProductSpace.HarmonicOnNhd vU (H \ extHullSet (U ω) (F ω)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ extHullSet (U ω) (F ω) →
        gU ω φ = ∫ z, vU z * φ z) → ∀ outer inner : Chart,
      outer.IsConformal → inner.IsConformal → (inner.dom : Set ℂ) ⊆ outer.dom →
      (outer.dom : Set ℂ) = C ω ∩ (H \ F ω) →
      (inner.dom : Set ℂ) = U ω ∩ (H \ F ω) → ∀ (p : ℂ) (ξ r : ℝ),
      p ∈ extHullSet (C ω) (F ω) ∪ {z : ℂ | z.im = 0} →
      (∃ ε > 0, C ω ∩ ball p ε = U ω ∩ ball p ε) → 0 < r →
      H ∩ ball (ξ : ℂ) r ⊆ ((pocketTransitionChart outer inner).dom : Set ℂ) →
      Tendsto outer.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
      Tendsto (fun z => vU (outer.2.1 z) - vC (outer.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_sub_of_marked_union hh hCm hUm hCloc hUloc hPairMarked
    hCunb hUunb hgC hgU] with ω hcompare vC vU hvC hvCr hvU hvUr
      outer inner hO hI hIncl hOC hIC p ξ r hp hLocal hr hCollar hLanding
  obtain ⟨ε, hε, heq⟩ := hLocal
  have hfilled := extHullSet_inter_ball_eq_of_pocket_agreement (F := F ω) heq
  obtain ⟨hUC, hCU⟩ := local_agreement_of_inter_ball_eq hε hfilled
  have hpU : p ∈ extHullSet (U ω) (F ω) ∪ {z : ℂ | z.im = 0} := by
    rcases hp with hp | hp
    · exact Or.inl (show p ∈ extHullSet (U ω) (F ω) from
        (hfilled ▸ (show p ∈ extHullSet (C ω) (F ω) ∩ ball p ε from ⟨hp, mem_ball_self hε⟩)).1)
    · exact Or.inr hp
  have hsub := hcompare vC vU hvC hvCr hvU hvUr p hp hpU hUC hCU
  have happroach := tendsto_inverse_common_complement hO hI hIncl hOC hIC hr hCollar hLanding
  simpa only [neg_sub, neg_zero, Function.comp_def] using (hsub.comp happroach).neg

end InteractingSLE.Sec7.PocketStopSide
