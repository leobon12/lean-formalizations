/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainRecord

/-!
# The pair-marked filled law from the joint walls and original hull

PROVE-POCKET-SIDEIN. Both records are retained before choosing a nested
witness. Enlarging the joint exploration to the union of the two filled
sets supplies its marked law; neither nesting nor independence is needed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

open LocalSets WholeField PocketUnionPt WangWu

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {MO MU : Set Ω} {C U Γ F : Ω → Set ℂ}

/-- The two filled sets retain the Gaussian marked law of the joint
exploration. The wall-cover premise only concerns the two fixed candidate events. -/
theorem retained_pair_law_of_joint_walls
    (hCRecord : Measurable[ℋ, hittingSigma] (eventFilled MO C F))
    (hURecord : Measurable[ℋ, hittingSigma] (eventFilled MU U F))
    (hCover : ∀ ω ∈ MO, ω ∈ MU → H ∩ Γ ω ⊆ (C ω)ᶜ ∪ (U ω)ᶜ)
    (hJoint : IsHistoryAvoidanceLocal ℋ (fun ω => H ∩ (Γ ω ∪ F ω)) h P) :
    IsHistoryAvoidanceLocal ℋ
      (fun ω => eventFilled MO C F ω ∪ eventFilled MU U F ω) h P := by
  refine Lemma72C.isHistoryAvoidanceLocal_mono_set hJoint
    (@measurable_union_hitting Ω ℋ _ _ hCRecord hURecord) (Eventually.of_forall ?_)
  intro ω z hz
  by_cases hO : ω ∈ MO
  · by_cases hU : ω ∈ MU
    · simp only [eventFilled, hO, hU, ↓reduceIte]
      rcases hz.2 with hzΓ | hzF
      · rcases hCover ω hO hU ⟨hz.1, hzΓ⟩ with hzC | hzU
        · exact Or.inl ⟨hz.1, Or.inl hzC⟩
        · exact Or.inr ⟨hz.1, Or.inl hzU⟩
      · exact Or.inl ⟨hz.1, Or.inr hzF⟩
    · exact Or.inr (by simpa only [eventFilled, hU, ↓reduceIte] using hz.1)
  · exact Or.inl (by simpa only [eventFilled, hO, ↓reduceIte] using hz.1)

/-- Restricting the retained marks gives exactly the two-set marked law
used by the R.5 comparison, with no retained restart law as input. -/
theorem pair_marked_law_of_joint_walls
    (hCRecord : Measurable[ℋ, hittingSigma] (eventFilled MO C F))
    (hURecord : Measurable[ℋ, hittingSigma] (eventFilled MU U F))
    (hCover : ∀ ω ∈ MO, ω ∈ MU → H ∩ Γ ω ⊆ (C ω)ᶜ ∪ (U ω)ᶜ)
    (hJoint : IsHistoryAvoidanceLocal ℋ (fun ω => H ∩ (Γ ω ∪ F ω)) h P) :
    IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (eventFilled MO C F) hittingSigma ⊔
        MeasurableSpace.comap (eventFilled MU U F) hittingSigma)
      (fun ω => eventFilled MO C F ω ∪ eventFilled MU U F ω) h P :=
  IsHistoryAvoidanceLocal.mono_marks
    (retained_pair_law_of_joint_walls hCRecord hURecord hCover hJoint)
    (sup_le hCRecord.comap_le hURecord.comap_le)

/-- The outer filled germ can also be retained. It is a smaller set than
the union even when neither initial pocket contains the other. -/
theorem pair_marked_law_with_germ_of_joint_walls [IsProbabilityMeasure P]
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hℋ : ℋ ≤ mΩ)
    (hCRecord : Measurable[ℋ, hittingSigma] (eventFilled MO C F))
    (hURecord : Measurable[ℋ, hittingSigma] (eventFilled MU U F))
    (hCover : ∀ ω ∈ MO, ω ∈ MU → H ∩ Γ ω ⊆ (C ω)ᶜ ∪ (U ω)ᶜ)
    (hJoint : IsHistoryAvoidanceLocal ℋ (fun ω => H ∩ (Γ ω ∪ F ω)) h P) :
    IsHistoryAvoidanceLocal
      ((MeasurableSpace.comap (eventFilled MO C F) hittingSigma ⊔
        MeasurableSpace.comap (eventFilled MU U F) hittingSigma) ⊔
        germSigma (eventFilled MO C F) h)
      (fun ω => eventFilled MO C F ω ∪ eventFilled MU U F ω) h P := by
  have hLaw := retained_pair_law_of_joint_walls hCRecord hURecord hCover hJoint
  have hAug := Lemma725RefMarks.isHistoryAvoidanceLocal_sup_germSigma hh hℋ
    ((@measurable_union_hitting Ω ℋ _ _ hCRecord hURecord).mono hℋ le_rfl)
    hLaw hCRecord (fun _ _ hz => Or.inl hz.1)
  exact IsHistoryAvoidanceLocal.mono_marks hAug
    (sup_le_sup_right (sup_le hCRecord.comap_le hURecord.comap_le) _)

end InteractingSLE.Sec7.PocketStopSide
