/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TaFillLoc

/-!
# Two closure properties of marked local sets: marked additions and the whole half-plane off a mark

Packet PROVE-GW2-RELDET, ruling R113 (`GW2SzLoc.SchedHullLocalStatement`). The explored trace of the schedule at a
physical time is the physical explored curve together with an addition determined by the explored path: the frozen
continuation after a piece's death. Off the event `oldSuccess` (a mark), the explored driver is the zero driver, whose
slit is NOT a local set for marks that carry the history (a deterministic set avoiding `U` would make every mark an
event of the field outside `U`). The way out, as in GB6's `retOfRec`, is to use the whole half-plane `ℍ` there.

* **`isHistoryAvoidanceLocal_union_marks`**: if `S` is marked local for field-determined marks `ℋ` and every
  avoidance event of `C` is a mark, then `S ∪ C` is marked local for `ℋ`, with marks as avoidance events;
* **`isHistoryAvoidanceLocal_ite_H`**: if `A` is marked local for `ℋ` with marks as avoidance events and `E` is a
  mark, then `A` on `E` and `ℍ` off `E` is marked local for `ℋ`, with marks as avoidance events.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open LocalSets WholeField

section Mix

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **A marked local set together with a set whose avoidance events are marks is marked local.** -/
theorem isHistoryAvoidanceLocal_union_marks (hhm : Measurable h) {S C : Ω → Set ℂ}
    (hloc : IsHistoryAvoidanceLocal ℋ S h P)
    (hSm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (S ω) U})
    (hCm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (C ω) U})
    (hℋd : ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (S ω ∪ C ω) U}) ∧
      IsHistoryAvoidanceLocal ℋ (fun ω => S ω ∪ C ω) h P := by
  have hev : ∀ U : Opens ℂ, {ω | Disjoint (S ω ∪ C ω) U} = {ω | Disjoint (S ω) U} ∩ {ω | Disjoint (C ω) U} := by
    intro U
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, disjoint_union_left]
  refine ⟨fun U hUH => by rw [hev U]; exact (hSm U hUH).inter (hCm U hUH),
    WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF => ?_⟩
  have e : {ω | Disjoint (S ω ∪ C ω) U} ∩ F = {ω | Disjoint (S ω) U} ∩ ({ω | Disjoint (C ω) U} ∩ F) := by
    rw [hev U, inter_assoc]
  rw [e]
  have hF' : MeasurableSet[ℋ] ({ω | Disjoint (C ω) U} ∩ F) := (hCm U hUH).inter hF
  exact WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc hUH hG hd hF'
    (hℋd _ ((hSm U hUH).inter hF'))

open scoped Classical in
/-- **A marked local set on a mark, the whole half-plane off it, is marked local.** -/
theorem isHistoryAvoidanceLocal_ite_H (hhm : Measurable h) {A : Ω → Set ℂ}
    (hloc : IsHistoryAvoidanceLocal ℋ A h P)
    (hAm : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (A ω) U})
    (hℋd : ℋ ≤ aeSigma (MeasurableSpace.comap h inferInstance) P) {E : Set Ω} (hE : MeasurableSet[ℋ] E) :
    (∀ U : Opens ℂ, (U : Set ℂ) ⊆ H →
      MeasurableSet[ℋ] {ω | Disjoint (if ω ∈ E then A ω else H) U}) ∧
      IsHistoryAvoidanceLocal ℋ (fun ω => if ω ∈ E then A ω else H) h P := by
  -- off `E` the set avoids `U` iff `U` is empty
  have hev : ∀ U : Opens ℂ, (U : Set ℂ) ⊆ H → (U : Set ℂ) ≠ ∅ →
      {ω | Disjoint (if ω ∈ E then A ω else H) U} = {ω | Disjoint (A ω) U} ∩ E := by
    intro U hUH hU
    ext ω
    by_cases hω : ω ∈ E
    · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, and_true]
    · simp only [hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, and_false, iff_false]
      intro hd
      obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.2 hU
      exact disjoint_left.1 hd (hUH hz) hz
  have hev0 : ∀ U : Opens ℂ, (U : Set ℂ) = ∅ → ∀ X : Ω → Set ℂ, {ω | Disjoint (X ω) U} = univ := by
    intro U hU X
    ext ω
    simp only [hU, mem_ofPred_eq, disjoint_empty, mem_univ]
  refine ⟨fun U hUH => ?_, WalkLaw.isHistoryAvoidanceLocal_of_mem_aeSigma hhm fun U G hUH hG hd F hF => ?_⟩
  · by_cases hU : (U : Set ℂ) = ∅
    · rw [hev0 U hU]
      exact MeasurableSet.univ
    · rw [hev U hUH hU]
      exact (hAm U hUH).inter hE
  · by_cases hU : (U : Set ℂ) = ∅
    · have e : {ω | Disjoint (if ω ∈ E then A ω else H) U} ∩ F = {ω | Disjoint (A ω) U} ∩ F := by
        rw [hev0 U hU, hev0 U hU]
      rw [e]
      exact WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc hUH hG hd hF (hℋd _ ((hAm U hUH).inter hF))
    · have e : {ω | Disjoint (if ω ∈ E then A ω else H) U} ∩ F = {ω | Disjoint (A ω) U} ∩ (E ∩ F) := by
        rw [hev U hUH hU, inter_assoc]
      rw [e]
      have hF' : MeasurableSet[ℋ] (E ∩ F) := hE.inter hF
      exact WalkLaw.mem_aeSigma_of_isHistoryAvoidanceLocal hhm hloc hUH hG hd hF'
        (hℋd _ ((hAm U hUH).inter hF'))

end Mix

end InteractingSLE.Theorem14.GW2Rd
