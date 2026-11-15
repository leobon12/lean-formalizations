/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutMarked
import InteractingSLE.Spec.Sec7.HOuterUnion

/-!
# The enlarged relative hull law after cutting out a retained reference

PROVE-R5-OUTER, R88. Apply the existing relative-hull avoidance criterion
to `C ∩ (H \ B)`, with the old reference `B` added to the walls. If the
ambient enlarged hull contains `B`, its marked walls law is unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open PocketTraversal PocketAdapt PocketCoupling PocketUnionPt PocketStop PocketStopField Lemma71C

/-- An incident relative hull already contains the exterior of every larger pocket. -/
theorem extHullSet_relHull_of_subset {C D : Set ℂ} (hDC : D ⊆ C) (ψ : ℂ → ℂ)
    (γ : ℝ → ℂ) (q : ℝ≥0) : extHullSet C (HOuter.relHull D ψ γ q) = HOuter.relHull D ψ γ q := by
  ext z
  simp only [extHullSet, HOuter.relHull, mem_inter_iff, mem_union, mem_compl_iff, Set.mem_sdiff, mem_preimage]
  tauto

/-- Relative hull union laws after removing a retained reference from the pocket.
The geometric hypotheses concern the cut incident domain and its explored prefix. -/
theorem pocketStopUnionLaw_relativeCut {Ω : Type*} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ} {q : ℝ≥0} (h𝓦 : 𝓦 ≤ mΩ)
    (hpre : locPrefixSigma 𝓦 A γ q ≤ mΩ) {C Γ F₀ B : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}
    (hCo : ∀ ω ∈ A, IsOpen (C ω))
    (hBo : ∀ ω ∈ A, IsOpen (H \ B ω))
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω ∩ (H \ B ω)})
    (hψm : ∀ z, Measurable[𝓦]
      ({ω | ω ∈ A ∧ z ∈ C ω ∩ (H \ B ω)}.indicator fun ω => ψ ω z))
    (hΓC : ∀ ω ∈ A, Disjoint (H ∩ Γ ω) (C ω))
    (hfr : ∀ ω ∈ A, frontier (C ω) ∩ H ⊆ Γ ω)
    (hψc : ∀ ω ∈ A, ContinuousOn (ψ ω) (C ω))
    (hψH : ∀ ω ∈ A, MapsTo (ψ ω) (C ω) H)
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω))
    (hBF : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → B ω ⊆ F₀ ω)
    (hDF : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      (C ω ∩ (H \ B ω)) ∩ ψ ω ⁻¹' (H \ QuantumZipper.fwdHull
        (fun s : ℝ => segDriver (γ ω) s.toNNReal) q) ⊆ H \ F₀ ω)
    (hZF : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → ∀ y ∈ C ω ∩ (H \ B ω),
      ψ ω y ∈ γ ω '' Icc 0 (capInv (γ ω) q) → y ∈ F₀ ω)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hW : PocketStopWallsLaw 𝓦 P A γ Γ F₀ h₀ q) :
    PocketStopUnionLaw 𝓦 P A γ C
      (fun ω => HOuter.relHull (C ω ∩ (H \ B ω)) (ψ ω) (γ ω) q) h₀ q := by
  have hΓD : ∀ ω ∈ A, Disjoint (H ∩ (Γ ω ∪ B ω)) (C ω ∩ (H \ B ω)) := by
    intro ω hω
    refine Set.disjoint_left.2 ?_
    rintro z ⟨hzH, hzΓ | hzB⟩ hzD
    · exact Set.disjoint_left.1 (hΓC ω hω) ⟨hzH, hzΓ⟩ hzD.1
    · exact hzD.2.2 hzB
  have hfrD : ∀ ω ∈ A, frontier (C ω ∩ (H \ B ω)) ∩ H ⊆ Γ ω ∪ B ω := by
    intro ω hω z hz
    rcases frontier_inter_subset (C ω) (H \ B ω) hz.1 with hC | hB
    · exact Or.inl (hfr ω hω ⟨hC.1, hz.2⟩)
    · refine Or.inr ?_
      by_contra hzB
      have hb := hB.2
      rw [(hBo ω hω).frontier_eq] at hb
      exact hb.2 ⟨hz.2, hzB⟩
  have hW' : PocketStopWallsLaw 𝓦 P A γ (fun ω => Γ ω ∪ B ω) F₀ h₀ q := by
    obtain ⟨E, hEm, hEloc, hEeq⟩ := hW
    refine ⟨E, hEm, hEloc, fun ω hω hq => ?_⟩
    rw [hEeq ω hω hq]
    ext z
    simp only [mem_inter_iff, mem_union]
    have hs := hBF ω hω hq
    tauto
  obtain ⟨E, hEm, hEloc, hEeq⟩ := HOuter.pocketStopUnionLaw_relHull_of_wallsLaw h𝓦 hpre hCm hψm
    (fun ω hω => (hCo ω hω).inter (hBo ω hω)) hΓD hfrD
    (fun ω hω => (hψc ω hω).mono inter_subset_left)
    (fun ω hω => (hψH ω hω).mono_left inter_subset_left) hγ hDF hZF hW'
  refine ⟨E, hEm, hEloc, fun ω hω hq => ?_⟩
  rw [hEeq ω hω hq, extHullSet_relHull_of_subset inter_subset_left,
    extHullSet_relHull_of_subset Subset.rfl]

end InteractingSLE.Sec7.R5Out
