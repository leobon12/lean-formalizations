/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TcCurve

/-!
# The Markov decomposition of the empty set, and marked local sets read on a mark

Packet PROVE-GW2-RELDET (`GW2TcCurve.SchedPhysCurveStatement`).

* **`ae_markovCompl_eq_self_of_empty`**: for an empty open set, the projection part of any Markov decomposition
  vanishes almost surely (it vanishes outside the closure of the set, here everywhere). So the complementary
  projection is the field itself.
* `mem_complSigma_of_empty`: every event determined by the field is an event of the complementary projection of the
  empty set.
* **`isHistoryAvoidanceLocal_ite_H_trace`**: let `A` be marked local for field-determined marks `ℋ₀` and `E` a mark of
  `ℋ₀`. Let the marks `ℋ` be field-determined, and on `E` almost surely those of `ℋ₀` (`∀ F ∈ ℋ, ∃ F₀ ∈ ℋ₀,
  E ∩ F =ᵐ E ∩ F₀`). Then `A` on `E`, `ℍ` off `E`, is marked local for `ℋ`. This is the form needed when the marks
  carry information (the canonical records of pieces never launched) that the explored set only carries on the success
  event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets WholeField

section Empty

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **For an empty open set the complementary projection is the field.** -/
theorem ae_markovCompl_eq_self_of_empty {U : Opens ℂ} (hU : (U : Set ℂ) = ∅)
    {h : Ω → DistOn upperHalfPlaneOpens} {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) :
    ∀ᵐ ω ∂P, markovCompl G (h ω) = h ω := by
  have hout : GFF.outsideOpens U upperHalfPlaneOpens = upperHalfPlaneOpens := by
    ext z
    simp [GFF.outsideOpens, hU]
  filter_upwards [hd.ae_restrictDist_outside_eq_zero] with ω hω
  rw [hout] at hω
  have hG : G (h ω) = 0 := by
    ext φ
    have h1 := congrArg (fun T : DistOn upperHalfPlaneOpens => T φ) hω
    simp only [GFF.restrictDist_apply] at h1
    have he : GFF.testIncl upperHalfPlaneOpens upperHalfPlaneOpens φ = φ :=
      DFunLike.coe_injective (GFF.coe_testIncl le_rfl φ)
    rw [he] at h1
    simpa using h1
  simp [markovCompl, hG]

/-- Every event determined by the field is an event of the complementary projection of the empty set. -/
theorem mem_complSigma_of_empty {U : Opens ℂ} (hU : (U : Set ℂ) = ∅) {h : Ω → DistOn upperHalfPlaneOpens}
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hd : GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun ω => G (h ω)) P) {F : Set Ω}
    (hF : MeasurableSet[aeSigma (MeasurableSpace.comap h inferInstance) P] F) :
    MeasurableSet[aeSigma (MeasurableSpace.comap (fun ω => markovCompl G (h ω)) inferInstance) P] F := by
  have hae : h =ᵐ[P] (id : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens) ∘
      fun ω => markovCompl G (h ω) := by
    filter_upwards [ae_markovCompl_eq_self_of_empty hU hd] with ω hω
    exact hω.symm
  have h1 := WalkLaw.comap_le_aeSigma_of_ae_eq_comp (P := P) measurable_id hae
  exact aeSigma_aeSigma_le _ _ (WalkLaw.aeSigma_mono h1 _ hF)

end Empty

section Trace

variable {Ω : Type*} {ℋ ℋ₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

open scoped Classical in
/-- **A marked local set on a mark, `ℍ` off it, is marked local for marks agreeing with its own on the mark.** -/
theorem isHistoryAvoidanceLocal_ite_H_trace (hhm : Measurable h) {A : Ω → Set ℂ}
    (hloc : IsHistoryAvoidanceLocal ℋ₀ A h P)
    (hAm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ₀] {ω | Disjoint (A ω) U})
    (hℋ₀d : ℋ₀ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P)
    (hℋd : ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P) {E : Set Ω} (hE : MeasurableSet[ℋ₀] E)
    (htr : ∀ F : Set Ω, MeasurableSet[ℋ] F → ∃ F₀ : Set Ω, MeasurableSet[ℋ₀] F₀ ∧ E ∩ F =ᵐ[P] E ∩ F₀) :
    IsHistoryAvoidanceLocal ℋ (fun ω => if ω ∈ E then A ω else H) h P := by
  refine WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF => ?_
  by_cases hU : (U : Set ℂ) = ∅
  · have e : {ω | Disjoint (if ω ∈ E then A ω else H) U} ∩ F = F := by
      ext ω
      simp only [hU, mem_inter_iff, mem_ofPred_eq, disjoint_empty, true_and]
    rw [e]
    exact mem_complSigma_of_empty hU hd (hℋd _ hF)
  · obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hU
    obtain ⟨F₀, hF₀, hEF⟩ := htr F hF
    have hEF₀ : MeasurableSet[ℋ₀] (E ∩ F₀) := hE.inter hF₀
    have h1 := WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc hUH hG hd hEF₀
      (hℋ₀d _ ((hAm U hUH).inter hEF₀))
    refine aeSigma_of_ae_eq h1 ?_
    filter_upwards [hEF] with ω hω
    have hω' : (ω ∈ E ∩ F) = (ω ∈ E ∩ F₀) := hω
    change (ω ∈ {ω | Disjoint (if ω ∈ E then A ω else H) U} ∩ F) = (ω ∈ {ω | Disjoint (A ω) U} ∩ (E ∩ F₀))
    by_cases hωE : ω ∈ E
    · simp only [mem_inter_iff, hωE, true_and, ↓reduceIte, mem_ofPred_eq] at hω' ⊢
      rw [hω']
    · simp only [mem_inter_iff, hωE, false_and, ↓reduceIte, mem_ofPred_eq, and_false]
      apply propext
      constructor
      · rintro ⟨hd', -⟩
        exact absurd hz (disjoint_left.1 hd' (hUH hz))
      · exact False.elim

end Trace

end InteractingSLE.Theorem14.GW2Rd
