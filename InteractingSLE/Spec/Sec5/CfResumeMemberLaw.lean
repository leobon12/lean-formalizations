/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfResumeMembers

/-!
# The locality identity on spaces with the same law

Packet PROVE-CFCHART2, continuation. Pull back the member identities through a measurable
map, using the actual pushforward measure. Measurability of the safe event is explicit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfResume

open Restart.DomainMarkov Restart.DomainMarkov.K2 Coupling LocalSets

variable {Z : Type*} [mZ : MeasurableSpace Z] {𝓩 : Filtration ℝ≥0 mZ}
  {F : Set Z} {ζ : Z → ℝ≥0∞} {W : ℝ≥0 → Z → ℝ}
  {X : Z → DistOn upperHalfPlaneOpens}

/-- The raw safe event is measurable for an adapted driver continuous before its lifetime. -/
theorem measurableSet_safeEv_of_adaptedBefore (hWa : AdaptedBefore 𝓩 ζ W)
    (hWc : ∀ z, ContinuousOn (fun t => W t z) {t | (t : ℝ≥0∞) < ζ z})
    (hW0 : ∀ z, W 0 z = 0) (s : ℝ≥0) {Fb : Finset (ℚ × ℚ × ℚ)}
    (hFb : ballsK Fb ⊆ QuantumZipper.H) : MeasurableSet[𝓩 s] (safeEv W ζ Fb s) := by
  have he : safeEv W ζ Fb s = safeU W ζ univ (indK Fb) s := by
    ext z
    exact (mem_safeU_indK_iff (hWc z) (hW0 z) hFb s).symm
  rw [he]
  exact measurableSet_safeU_indK hWa hWc hFb s

/-- Locality for pulled-back data is equivalent to locality for their pushforward law.
The measurable safe event is needed when moving almost sure avoidance to that law. -/
theorem hasSafeMembers_comap_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → Z} (hg : Measurable g) (hF : MeasurableSet F) (hX : Measurable X)
    (hS : ∀ s Fb, ballsK Fb ⊆ QuantumZipper.H → MeasurableSet (safeEv W ζ Fb s)) :
    HasSafeMembers P (filtrationComap 𝓩 hg) (g ⁻¹' F) (ζ ∘ g)
        (fun t ω => W t (g ω)) (X ∘ g) ↔
      HasSafeMembers (P.map g) 𝓩 F ζ W X := by
  have hm : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable (fun z => Complex.exp (Complex.I * (X z φ : ℂ))) := fun φ =>
    GFF.measurable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hX)
  constructor
  · intro h s Fb hFb D hD hsafe f Ξ
    have hs := ae_of_ae_map hg.aemeasurable hsafe
    have key := h s Fb hFb (g ⁻¹' D) (by exact ⟨D, hD, rfl⟩) hs f Ξ
    rw [setIntegral_map (𝓩.le s D hD) (hm _).aestronglyMeasurable hg.aemeasurable,
      setIntegral_map (𝓩.le s D hD) (hm _).aestronglyMeasurable hg.aemeasurable]
    exact key
  · intro h s Fb hFb D hD hsafe f Ξ
    obtain ⟨D₀, hD₀, rfl⟩ := hD
    have hsafeM : MeasurableSet {z | z ∈ D₀ → z ∈ F ∧ (s : ℝ≥0∞) < ζ z ∧
        Disjoint (ballsK Fb) (QuantumZipper.fwdHull
          (fun r : ℝ => W r.toNNReal z) (s : ℝ))} := by
      have he : {z | z ∈ D₀ → z ∈ F ∧ (s : ℝ≥0∞) < ζ z ∧
          Disjoint (ballsK Fb) (QuantumZipper.fwdHull
            (fun r : ℝ => W r.toNNReal z) (s : ℝ))} = D₀ᶜ ∪ (F ∩ safeEv W ζ Fb s) := by
        ext z
        simp only [mem_ofPred_eq, mem_union, mem_compl_iff, mem_inter_iff, safeEv]
        tauto
      rw [he]
      exact (𝓩.le s D₀ hD₀).compl.union (hF.inter (hS s Fb hFb))
    have hs : ∀ᵐ z ∂P.map g, z ∈ D₀ → z ∈ F ∧ (s : ℝ≥0∞) < ζ z ∧
        Disjoint (ballsK Fb) (QuantumZipper.fwdHull
          (fun r : ℝ => W r.toNNReal z) (s : ℝ)) :=
      (ae_map_iff hg.aemeasurable hsafeM).2 hsafe
    have key := h s Fb hFb D₀ hD₀ hs f Ξ
    rw [setIntegral_map (𝓩.le s D₀ hD₀) (hm _).aestronglyMeasurable hg.aemeasurable,
      setIntegral_map (𝓩.le s D₀ hD₀) (hm _).aestronglyMeasurable hg.aemeasurable] at key
    exact key

/-- The member identities move between two spaces with the same joint law of all data. -/
theorem hasSafeMembers_of_map_eq {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    {g₁ : Ω₁ → Z} (hg₁ : Measurable g₁) {Ω₂ : Type*} [MeasurableSpace Ω₂]
    {P₂ : Measure Ω₂} {g₂ : Ω₂ → Z} (hg₂ : Measurable g₂)
    (hlaw : P₁.map g₁ = P₂.map g₂) (hF : MeasurableSet F) (hX : Measurable X)
    (hS : ∀ s Fb, ballsK Fb ⊆ QuantumZipper.H → MeasurableSet (safeEv W ζ Fb s))
    (h : HasSafeMembers P₁ (filtrationComap 𝓩 hg₁) (g₁ ⁻¹' F) (ζ ∘ g₁)
      (fun t ω => W t (g₁ ω)) (X ∘ g₁)) :
    HasSafeMembers P₂ (filtrationComap 𝓩 hg₂) (g₂ ⁻¹' F) (ζ ∘ g₂)
      (fun t ω => W t (g₂ ω)) (X ∘ g₂) := by
  have hQ := (hasSafeMembers_comap_iff hg₁ hF hX hS).1 h
  rw [hlaw] at hQ
  exact (hasSafeMembers_comap_iff hg₂ hF hX hS).2 hQ

/-- Equal-law transport with the safe-event measurability discharged by driver regularity. -/
theorem hasSafeMembers_of_map_eq_of_adaptedBefore
    {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} {g₁ : Ω₁ → Z}
    (hg₁ : Measurable g₁) {Ω₂ : Type*} [MeasurableSpace Ω₂] {P₂ : Measure Ω₂}
    {g₂ : Ω₂ → Z} (hg₂ : Measurable g₂) (hlaw : P₁.map g₁ = P₂.map g₂)
    (hF : MeasurableSet F) (hX : Measurable X) (hWa : AdaptedBefore 𝓩 ζ W)
    (hWc : ∀ z, ContinuousOn (fun t => W t z) {t | (t : ℝ≥0∞) < ζ z})
    (hW0 : ∀ z, W 0 z = 0)
    (h : HasSafeMembers P₁ (filtrationComap 𝓩 hg₁) (g₁ ⁻¹' F) (ζ ∘ g₁)
      (fun t ω => W t (g₁ ω)) (X ∘ g₁)) :
    HasSafeMembers P₂ (filtrationComap 𝓩 hg₂) (g₂ ⁻¹' F) (ζ ∘ g₂)
      (fun t ω => W t (g₂ ω)) (X ∘ g₂) :=
  hasSafeMembers_of_map_eq hg₁ hg₂ hlaw hF hX
    (fun s _ hFb => 𝓩.le s _ (measurableSet_safeEv_of_adaptedBefore hWa hWc hW0 s hFb)) h

end InteractingSLE.Sec5.CfResume
