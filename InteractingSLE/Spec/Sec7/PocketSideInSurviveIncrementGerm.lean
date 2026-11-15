/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveIncrementLaw

/-!
# The initial-to-current physical mean germ

PROVE-POCKET-SIDEIN. Local activity of the initial pocket supplies equality
of the two filled-set germs. The retained comparison theorem then gives the
old-to-current mean increment along every finite current inverse access.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Bornology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketUnionPt

/-- A uniform marked germ comparison for initial/current cuts of one
fixed candidate. Survival will supply the local activity premise. -/
theorem ae_initial_current_germ_of_local_activity {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {M : Set Ω} {C F : Ω → Set ℂ}
    (hm0 : Measurable[mΩ, hittingSigma] (eventFilled M C (fun _ => ∅)))
    (hmq : Measurable[mΩ, hittingSigma] (eventFilled M C F))
    (hl0 : IsLocalSet (eventFilled M C (fun _ => ∅)) h P)
    (hlq : IsLocalSet (eventFilled M C F) h P)
    (hPair : IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (eventFilled M C (fun _ => ∅)) hittingSigma ⊔
        MeasurableSpace.comap (eventFilled M C F) hittingSigma)
      (fun ω => eventFilled M C (fun _ => ∅) ω ∪ eventFilled M C F ω) h P)
    (hu0 : ∀ᵐ ω ∂P, ∀ p ∈ lowerUnion (eventFilled M C (fun _ => ∅) ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (eventFilled M C (fun _ => ∅) ω)) p))
    (huq : ∀ᵐ ω ∂P, ∀ p ∈ lowerUnion (eventFilled M C F ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (eventFilled M C F ω)) p))
    {g0 gq : Ω → DistOn upperHalfPlaneOpens}
    (hg0 : IsLocalSetMean (eventFilled M C (fun _ => ∅)) h P g0)
    (hgq : IsLocalSetMean (eventFilled M C F) h P gq) :
    ∀ᵐ ω ∂P, ω ∈ M → ∀ v0 vq : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v0 (H \ eventFilled M C (fun _ => ∅) ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ eventFilled M C (fun _ => ∅) ω →
        g0 ω φ = ∫ z, v0 z * φ z) →
      InnerProductSpace.HarmonicOnNhd vq (H \ eventFilled M C F ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ eventFilled M C F ω →
        gq ω φ = ∫ z, vq z * φ z) → ∀ c : Chart,
      c.IsConformal → (c.dom : Set ℂ) = C ω ∩ (H \ F ω) → ∀ (p : ℂ) (ξ : ℝ),
      (∀ᶠ z in 𝓝[C ω] p, z ∈ (c.dom : Set ℂ)) →
      Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 p) →
      Tendsto (fun z => vq (c.2.1 z) - v0 (c.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  filter_upwards [ae_tendsto_sub_of_marked_union hh hm0 hmq hl0 hlq hPair hu0 huq hg0 hgq]
    with ω hCompare hω v0 vq hv0 hRep0 hvq hRepq c hc hDomain p ξ hActive hLanding
  obtain ⟨ε, hε, hEq⟩ := filled_initial_agreement_of_active_neighborhood hDomain hActive
  have hFilled : eventFilled M C (fun _ => ∅) ω ∩ ball p ε =
      eventFilled M C F ω ∩ ball p ε := by
    simpa only [eventFilled, hω, ↓reduceIte] using hEq.symm
  obtain ⟨hQ0, h0Q⟩ := local_agreement_of_inter_ball_eq hε hFilled
  have hpq : p ∈ eventFilled M C F ω ∪ {z : ℂ | z.im = 0} := by
    simpa only [eventFilled, hω, ↓reduceIte] using
      inverse_real_landing_mem_filled_or_real hc hDomain hLanding
  have hp0 : p ∈ eventFilled M C (fun _ => ∅) ω ∪ {z : ℂ | z.im = 0} := by
    rcases hpq with hpq | hpReal
    · exact Or.inl (hFilled.symm ▸ (show p ∈ eventFilled M C F ω ∩ ball p ε from
        ⟨hpq, mem_ball_self hε⟩)).1
    · exact Or.inr hpReal
  have hGerm := hCompare v0 vq hv0 hRep0 hvq hRepq p hp0 hpq hQ0 h0Q
  have hApproach : Tendsto c.2.1 (𝓝[H] (ξ : ℂ))
      (𝓝[H \ (eventFilled M C (fun _ => ∅) ω ∪ eventFilled M C F ω)] p) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hLanding, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hmem : c.2.1 z ∈ (c.dom : Set ℂ) := hc.inv_mem_dom hz
    rw [hDomain] at hmem
    simp only [eventFilled, hω, ↓reduceIte]
    exact ⟨hmem.2.1, fun hbad => hbad.elim
      (fun hb => hb.2.elim (fun hn => hn hmem.1) False.elim)
      (fun hb => hb.2.elim (fun hn => hn hmem.1) hmem.2.2)⟩
  simpa only [Function.comp_def, neg_sub, neg_zero] using (hGerm.comp hApproach).neg

end InteractingSLE.Sec7.PocketStopSide
