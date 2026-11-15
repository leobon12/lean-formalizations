/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA15Rect

/-!
# A.1.5: the curve marginals up to the last exit are the same in every larger family

Packet PROVE-ZHAN-GT4-A18. Source: Astra, *Follow-up proofs*, §A.1.5 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L409–L425, R38): the couplings of the first `n` enclosure pairs are couplings of the *fixed* marginal path laws. In the
Lean set-up the curve-`1` marginal of the stopped dual coupling of a finite family is the force-point law up to the last
exit `max_i S₁ i` (A17's `exists_forceLaw₁`); this file shows that a larger family has the same curve-`1` marginal on
the σ-algebra of that last exit (and symmetrically for curve `2`), so the marginal laws of every finite block of
recorded coordinates are eventually fixed.

Route: partition by the first index attaining the last exit (`firstMaxSet`); on that event the last exit is the
stopping time of one rectangle, the event is measurable at that rectangle's time, and A18's per-rectangle consistency
`dualCoupling_congr_of_rect` applies.

* `firstMaxSet`, `iUnion_firstMaxSet`, `pairwise_disjoint_firstMaxSet`, `lastExit_eq_of_mem_firstMaxSet`;
* `measurableSet_inter_firstMaxSet`: `A ∩ firstMaxSet S i` is measurable at `S i` for `A` measurable at the last exit;
* **`DualHyp.dualCoupling_fst_congr`**, **`DualHyp.dualCoupling_snd_congr`**: for a family `ι` embedded in a family `ι'`
  (same rectangles), the two stopped dual couplings agree on `A ×ˢ univ` for every event `A` of curve `1` at its last
  exit (resp. on `univ ×ˢ B`).
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-! ### The first index attaining the last exit -/

section FirstMax

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The event that `i` is the first index attaining `max_j S j`. -/
def firstMaxSet (S : ι → Ω → ℝ≥0) (i : ι) : Set Ω := {ω | (∀ j, S j ω ≤ S i ω) ∧ ∀ j, j < i → S j ω < S i ω}

omit [Fintype ι] in
theorem pairwise_disjoint_firstMaxSet (S : ι → Ω → ℝ≥0) : Pairwise fun i i' => Disjoint (firstMaxSet S i)
    (firstMaxSet S i') := by
  intro i i' hii'
  refine Set.disjoint_left.2 fun ω hω hω' => ?_
  rcases lt_or_gt_of_ne hii' with h | h
  · exact absurd (hω'.2 i h) (not_lt.2 (hω.1 i'))
  · exact absurd (hω.2 i' h) (not_lt.2 (hω'.1 i))

theorem iUnion_firstMaxSet [Nonempty ι] (S : ι → Ω → ℝ≥0) : ⋃ i, firstMaxSet S i = univ := by
  refine eq_univ_of_forall fun ω => ?_
  set M : Finset ι := univ.filter fun i => ∀ j, S j ω ≤ S i ω with hM
  have hMne : M.Nonempty := by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image univ (fun i => S i ω) univ_nonempty
    exact ⟨j, mem_filter.2 ⟨mem_univ _, fun i => hj i (mem_univ i)⟩⟩
  have hmin := M.min'_mem hMne
  refine mem_iUnion.2 ⟨M.min' hMne, (mem_filter.1 hmin).2, fun j hj => ?_⟩
  refine lt_of_le_of_ne ((mem_filter.1 hmin).2 j) fun he => ?_
  have hjM : j ∈ M := mem_filter.2 ⟨mem_univ _, fun l => by rw [he]; exact (mem_filter.1 hmin).2 l⟩
  exact absurd (M.min'_le j hjM) (not_le.2 hj)

omit [LinearOrder ι] in
theorem lastExit_eq_of_forall_le {S : ι → Ω → ℝ≥0} {ω : Ω} {i : ι} (h : ∀ j, S j ω ≤ S i ω) :
    lastExit S ω = S i ω :=
  le_antisymm ((lastExit_le_iff S ω _).2 h) (le_lastExit S ω i)

/-- **An event at the last exit, restricted to `firstMaxSet S i`, is an event at `S i`.** -/
theorem measurableSet_inter_firstMaxSet {𝓕 : Filtration ℝ≥0 mΩ} {S : ι → Ω → ℝ≥0}
    (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S i ω : WithTop ℝ≥0)) {A : Set Ω}
    (hA : MeasurableSet[(isStoppingTime_lastExit hS).measurableSpace] A) (i : ι) :
    MeasurableSet[(hS i).measurableSpace] (A ∩ firstMaxSet S i) := by
  have hL := isStoppingTime_lastExit hS
  -- the comparison events
  have hle : ∀ j, MeasurableSet[(hS i).measurableSpace] {ω | S j ω ≤ S i ω} := fun j => by
    have := (hS j).measurableSet_stopping_time_le (hS i)
    simpa only [WithTop.coe_le_coe] using this
  have hlt : ∀ j, MeasurableSet[(hS i).measurableSpace] {ω | S j ω < S i ω} := fun j => by
    have := ((hS i).measurableSet_le_stopping_time (hS j)).compl
    simpa only [WithTop.coe_le_coe, compl_ofPred, not_le] using this
  have hE : MeasurableSet[(hS i).measurableSpace] (firstMaxSet S i) := by
    have e : firstMaxSet S i = (⋂ j, {ω | S j ω ≤ S i ω}) ∩ ⋂ j, ⋂ (_ : j < i), {ω | S j ω < S i ω} := by
      ext ω; simp only [firstMaxSet, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    rw [e]
    exact (MeasurableSet.iInter hle).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => hlt j)
  have h1 : MeasurableSet[(hS i).measurableSpace] (A ∩ {ω | (lastExit S ω : WithTop ℝ≥0) ≤ S i ω}) :=
    ((hL.min (hS i)).measurableSpace_mono (hS i) fun ω => min_le_right _ _) _
      (hL.measurableSet_inter_le (hS i) A hA)
  have e : A ∩ firstMaxSet S i = (A ∩ {ω | (lastExit S ω : WithTop ℝ≥0) ≤ S i ω}) ∩ firstMaxSet S i := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hωA, hω⟩
      exact ⟨⟨hωA, WithTop.coe_le_coe.2 (lastExit_eq_of_forall_le hω.1).le⟩, hω⟩
    · rintro ⟨⟨hωA, -⟩, hω⟩
      exact ⟨hωA, hω⟩
  rw [e]
  exact h1.inter hE

end FirstMax

/-! ### The marginals of a family and of a larger family -/

section Dual

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {ι ι' : Type*} [Fintype ι]
  [LinearOrder ι] [Fintype ι'] {n : ℕ} {κ : ℝ} {P₁ : Measure Ω₁} {𝓕₁ : Filtration ℝ≥0 mΩ₁}
  {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂} {𝓕₂ : Filtration ℝ≥0 mΩ₂} {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ}
  {p : Fin n → ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {Tm : ℝ} {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}
  {H₁' H₂' : ι' → Set ℂ} {δ' q' d' : ι' → ℝ} {Tm' : ℝ} {S₁' : ι' → Ω₁ → ℝ≥0} {S₂' : ι' → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
  (h' : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁' H₂' δ' q' d' p Tm' S₁' S₂')
include h h'

/-- **The curve-`1` marginal on the σ-algebra of the last exit is the same in a larger family.** -/
theorem dualCoupling_fst_congr [Nonempty ι] [Nonempty ι'] (rr : Fin n → ℝ) (e : ι → ι')
    (h₁ : ∀ i, S₁' (e i) = S₁ i) (h₂ : ∀ i, S₂' (e i) = S₂ i) {A : Set Ω₁}
    (hA : MeasurableSet[(isStoppingTime_lastExit h.stop₁).measurableSpace] A) :
    dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁' S₂' Tm' (A ×ˢ univ) =
      dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm (A ×ˢ univ) := by
  have hAi : ∀ i, MeasurableSet[(h.stop₁ i).measurableSpace] (A ∩ firstMaxSet S₁ i) := fun i =>
    measurableSet_inter_firstMaxSet h.stop₁ hA i
  have hAm : ∀ i, MeasurableSet ((A ∩ firstMaxSet S₁ i) ×ˢ (univ : Set Ω₂)) := fun i =>
    ((h.stop₁ i).measurableSpace_le _ (hAi i)).prod MeasurableSet.univ
  have hU : A ×ˢ (univ : Set Ω₂) = ⋃ i, (A ∩ firstMaxSet S₁ i) ×ˢ (univ : Set Ω₂) := by
    rw [← iUnion_prod_const, ← inter_iUnion, iUnion_firstMaxSet, inter_univ]
  have hdisj : Pairwise fun i i' => Disjoint ((A ∩ firstMaxSet S₁ i) ×ˢ (univ : Set Ω₂))
      ((A ∩ firstMaxSet S₁ i') ×ˢ (univ : Set Ω₂)) := fun i i' hii' =>
    Set.disjoint_prod.2 (Or.inl (((pairwise_disjoint_firstMaxSet S₁ hii').mono inter_subset_right
      inter_subset_right)))
  rw [hU, measure_iUnion hdisj hAm, measure_iUnion hdisj hAm]
  refine tsum_congr fun i => ?_
  refine h.dualCoupling_congr_of_rect h' rr (h₁ i) (h₂ i) ?_
  exact @MeasurableSet.prod _ _ (h.stop₁ i).measurableSpace (h.stop₂ i).measurableSpace _ _ (hAi i)
    (@MeasurableSet.univ _ (h.stop₂ i).measurableSpace)

/-- **The curve-`2` marginal on the σ-algebra of the last exit is the same in a larger family.** -/
theorem dualCoupling_snd_congr [Nonempty ι] [Nonempty ι'] (rr : Fin n → ℝ) (e : ι → ι')
    (h₁ : ∀ i, S₁' (e i) = S₁ i) (h₂ : ∀ i, S₂' (e i) = S₂ i) {B : Set Ω₂}
    (hB : MeasurableSet[(isStoppingTime_lastExit h.stop₂).measurableSpace] B) :
    dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁' S₂' Tm' (univ ×ˢ B) =
      dualCoupling κ rr p P₁ B₁ P₂ B₂ x₂ S₁ S₂ Tm (univ ×ˢ B) := by
  have hBi : ∀ i, MeasurableSet[(h.stop₂ i).measurableSpace] (B ∩ firstMaxSet S₂ i) := fun i =>
    measurableSet_inter_firstMaxSet h.stop₂ hB i
  have hBm : ∀ i, MeasurableSet ((univ : Set Ω₁) ×ˢ (B ∩ firstMaxSet S₂ i)) := fun i =>
    MeasurableSet.univ.prod ((h.stop₂ i).measurableSpace_le _ (hBi i))
  have hU : (univ : Set Ω₁) ×ˢ B = ⋃ i, (univ : Set Ω₁) ×ˢ (B ∩ firstMaxSet S₂ i) := by
    rw [← prod_iUnion, ← inter_iUnion, iUnion_firstMaxSet, inter_univ]
  have hdisj : Pairwise fun i i' => Disjoint ((univ : Set Ω₁) ×ˢ (B ∩ firstMaxSet S₂ i))
      ((univ : Set Ω₁) ×ˢ (B ∩ firstMaxSet S₂ i')) := fun i i' hii' =>
    Set.disjoint_prod.2 (Or.inr (((pairwise_disjoint_firstMaxSet S₂ hii').mono inter_subset_right
      inter_subset_right)))
  rw [hU, measure_iUnion hdisj hBm, measure_iUnion hdisj hBm]
  refine tsum_congr fun i => ?_
  refine h.dualCoupling_congr_of_rect h' rr (h₁ i) (h₂ i) ?_
  exact @MeasurableSet.prod _ _ (h.stop₁ i).measurableSpace (h.stop₂ i).measurableSpace _ _
    (@MeasurableSet.univ _ (h.stop₁ i).measurableSpace) (hBi i)

end DualHyp

end Dual

end InteractingSLE.ZhanGT4
