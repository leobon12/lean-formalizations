/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRealLaws
import InteractingSLE.Spec.Sec7.PocketStopWallsFinStop

/-!
# Filled records at a fixed original time

PROVE-POCKET-SIDEIN. Normalize on a fixed candidate event, before selecting
any realized witness. The existing dense-point avoidance criterion constructs
the hitting record from the walls, hull and pocket membership events.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets PocketUnionPt PocketStopField

open Classical in
/-- The filled set at a fixed original time, with empty active domain off
the fixed candidate event. This normalization imposes no off-event nesting. -/
def eventFilled {Ω : Type*} (M : Set Ω) (C F : Ω → Set ℂ) (ω : Ω) : Set ℂ :=
  if ω ∈ M then extHullSet (C ω) (F ω) else H

/-- The existing walls avoidance identity constructs the complete hitting
record. Only fixed physical point membership in the initial pocket is used. -/
theorem measurable_eventFilled {Ω : Type*} {ℋ : MeasurableSpace Ω}
    {M : Set Ω} (hM : MeasurableSet[ℋ] M) {C Γ F : Ω → Set ℂ}
    (hPoint : ∀ z, MeasurableSet[ℋ] {ω | ω ∈ M ∧ z ∈ C ω})
    (hCo : ∀ ω ∈ M, IsOpen (C ω))
    (hDisjoint : ∀ ω ∈ M, Disjoint (H ∩ Γ ω) (C ω))
    (hFrontier : ∀ ω ∈ M, frontier (C ω) ∩ H ⊆ Γ ω)
    (hWallsHull : Measurable[ℋ, hittingSigma] (fun ω => H ∩ (Γ ω ∪ F ω))) :
    Measurable[ℋ, hittingSigma] (eventFilled M C F) := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  refine @measurable_generateFrom Ω (Set ℂ) ℋ _ _ ?_
  rintro _ ⟨V, hVo, hVH, rfl⟩
  rcases V.eq_empty_or_nonempty with rfl | hV
  · simpa only [inter_empty, Set.not_nonempty_empty, ofPred_false, preimage_empty] using
      (MeasurableSet.empty : MeasurableSet[ℋ] (∅ : Set Ω))
  have hAvoid : MeasurableSet[ℋ] {ω | Disjoint (H ∩ (Γ ω ∪ F ω)) V} :=
    hWallsHull (measurableSet_avoid hVo hVH)
  have hPoints := measurableSet_ptEvent hPoint e V
  have hEq : (eventFilled M C F) ⁻¹' {S : Set ℂ | (S ∩ V).Nonempty} =
      (M ∩ {ω | Disjoint (H ∩ (Γ ω ∪ F ω)) V} ∩ ptEvent M C e V)ᶜ := by
    ext ω
    rw [mem_preimage, mem_ofPred_eq, ← Set.not_disjoint_iff_nonempty_inter]
    by_cases hω : ω ∈ M
    · rw [eventFilled, ite_eq_left hω,
        disjoint_extHullSet_iff (hCo ω hω) (hDisjoint ω hω) (hFrontier ω hω) hVo hVH he]
      simp only [mem_compl_iff, mem_inter_iff, mem_ofPred_eq, ptEvent, hω, true_and]
    · have hNot : ¬ Disjoint H V := by
        obtain ⟨z, hz⟩ := hV
        exact fun hd => Set.disjoint_left.1 hd (hVH hz) hz
      simp [eventFilled, hω, hNot]
  rw [hEq]
  exact ((hM.inter hAvoid).inter hPoints).compl

/-- Both normalized records are regular whenever their active physical
domains are open on the fixed candidate event. -/
theorem eventFilled_regular {Ω : Type*} {M : Set Ω} {C F : Ω → Set ℂ}
    (hCo : ∀ ω ∈ M, IsOpen (C ω)) (hFo : ∀ ω ∈ M, IsOpen (H \ F ω)) (ω : Ω) :
    eventFilled M C F ω ⊆ H ∧ IsOpen (H \ eventFilled M C F ω) := by
  by_cases hω : ω ∈ M
  · rw [eventFilled, ite_eq_left hω]
    refine ⟨inter_subset_left, ?_⟩
    have he : H \ extHullSet (C ω) (F ω) = C ω ∩ (H \ F ω) := by
      ext z
      simp only [extHullSet, Set.mem_sdiff, mem_inter_iff, mem_union, mem_compl_iff]
      tauto
    rw [he]
    exact (hCo ω hω).inter (hFo ω hω)
  · rw [eventFilled, ite_eq_right hω, Set.sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩

end InteractingSLE.Sec7.PocketStopSide
