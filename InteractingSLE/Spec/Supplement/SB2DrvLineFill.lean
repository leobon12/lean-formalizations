/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvLineUnion
import InteractingSLE.Spec.Restart.RetPlumbProofFilled

/-!
# Fills of marked local sets with mark-measurable avoidance events

Packet PROVE-T14-SB2DRV (round 5), generic tools for SB2(1)'s line union (the filled retained prefix with the filled
upper flow, whose mean FIN's union-mean lemma computes). For a random set `C ⊆ ℍ` whose avoidance events of open
subsets of `ℍ` are events of a σ-algebra `ℋ`:

* **`isDyadicHitMeasurable_closure_of_avoid`**: the closure of `C` has `ℋ`-measurable dyadic hits;
* `measurableSet_isBounded_of_avoid`, `cptClosure` (the closure where bounded, `∅` elsewhere, compact at every
  sample), **`measurable_fillH_cptClosure`** (the fill is `ℋ`-hitting-measurable).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Lv

open Restart LocalSets

section Fill

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} {C : Ω → Set ℂ}

theorem isOpen_H' : IsOpen H := isOpen_lt continuous_const Complex.continuous_im

theorem isCompact_dyadicSquare (n : ℕ) (k : ℤ × ℤ) : IsCompact (dyadicSquare n k) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_dyadicSquare n k) ?_
  rw [Metric.isBounded_iff]
  exact ⟨2 / 2 ^ n, fun z hz w hw => by rw [dist_eq_norm]; exact norm_sub_le_of_mem_dyadicSquare hz hw⟩

/-- **Dyadic hits of the closure from the avoidance events.** -/
theorem isDyadicHitMeasurable_closure_of_avoid (hCH : ∀ ω, C ω ⊆ H)
    (hC : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (C ω) U}) :
    @IsDyadicHitMeasurable Ω ℋ fun ω => closure (C ω) := by
  intro n k
  set Q := dyadicSquare n k with hQ
  have hQc : IsCompact Q := isCompact_dyadicSquare n k
  let V : ℕ → TopologicalSpace.Opens ℂ := fun m =>
    ⟨thickening (1 / ((m : ℝ) + 1)) Q ∩ H, isOpen_thickening.inter isOpen_H'⟩
  have hVH : ∀ m, ((V m : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆ H := fun m => inter_subset_right
  have e : {ω | (Q ∩ closure (C ω)).Nonempty} = ⋂ m : ℕ, {ω | Disjoint (C ω) (V m)}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, mem_compl_iff]
    constructor
    · rintro ⟨z, hzQ, hzC⟩ m hd
      have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      obtain ⟨c, hcC, hcz⟩ := Metric.mem_closure_iff.1 hzC _ hε
      refine Set.disjoint_left.1 hd hcC ⟨?_, hCH ω hcC⟩
      exact mem_thickening_iff.2 ⟨z, hzQ, by rw [dist_comm]; exact hcz⟩
    · intro hall
      by_contra hne
      rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hne
      obtain ⟨δ, hδ, hδs⟩ := hQc.exists_thickening_subset_open isClosed_closure.isOpen_compl
        (fun z hz hzc => Set.disjoint_left.1 hne hz hzc)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine hall m (Set.disjoint_left.2 fun c hcC hcV => ?_)
      have hc1 : c ∈ thickening δ Q := thickening_mono hm.le Q hcV.1
      exact hδs hc1 (subset_closure hcC)
  show MeasurableSet[ℋ] {ω | (Q ∩ closure (C ω)).Nonempty}
  rw [e]
  exact MeasurableSet.iInter fun m => (hC (V m) (hVH m)).compl

/-- The boundedness event. -/
theorem measurableSet_isBounded_of_avoid (hCH : ∀ ω, C ω ⊆ H)
    (hC : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (C ω) U}) :
    MeasurableSet[ℋ] {ω | Bornology.IsBounded (C ω)} := by
  let V : ℕ → TopologicalSpace.Opens ℂ := fun R =>
    ⟨H \ closedBall 0 (R : ℝ), isOpen_H'.sdiff isClosed_closedBall⟩
  have e : {ω | Bornology.IsBounded (C ω)} = ⋃ R : ℕ, {ω | Disjoint (C ω) (V R)} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hb
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hb
      obtain ⟨N, hN⟩ := exists_nat_ge R
      refine ⟨N, Set.disjoint_left.2 fun z hz hzV => hzV.2 (closedBall_subset_closedBall hN (hR hz))⟩
    · rintro ⟨R, hR⟩
      refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := (R : ℝ))).subset fun z hz => ?_
      by_contra hn
      exact Set.disjoint_left.1 hR hz ⟨hCH ω hz, hn⟩
  rw [e]
  exact MeasurableSet.iUnion fun R => hC (V R) inter_subset_left

open Classical in
/-- The closure where bounded, `∅` elsewhere: compact at every sample. -/
def cptClosure (C : Ω → Set ℂ) (ω : Ω) : Set ℂ :=
  if Bornology.IsBounded (C ω) then closure (C ω) else ∅

theorem isCompact_cptClosure (C : Ω → Set ℂ) (ω : Ω) : IsCompact (cptClosure C ω) := by
  unfold cptClosure
  split_ifs with hb
  · exact Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure
  · exact isCompact_empty

theorem isDyadicHitMeasurable_cptClosure (hCH : ∀ ω, C ω ⊆ H)
    (hC : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (C ω) U}) :
    @IsDyadicHitMeasurable Ω ℋ (cptClosure C) := by
  classical
  intro n k
  have hB := measurableSet_isBounded_of_avoid hCH hC
  have hD := isDyadicHitMeasurable_closure_of_avoid hCH hC n k
  have e : {ω | (dyadicSquare n k ∩ cptClosure C ω).Nonempty} =
      {ω | Bornology.IsBounded (C ω)} ∩ {ω | (dyadicSquare n k ∩ closure (C ω)).Nonempty} := by
    ext ω
    by_cases hb : Bornology.IsBounded (C ω)
    · simp [cptClosure, hb]
    · simp [cptClosure, hb]
  show MeasurableSet[ℋ] {ω | (dyadicSquare n k ∩ cptClosure C ω).Nonempty}
  rw [e]
  exact hB.inter hD

/-- **The fill of the compact closure is `ℋ`-hitting-measurable.** -/
theorem measurable_fillH_cptClosure (hCH : ∀ ω, C ω ⊆ H)
    (hC : ∀ U : TopologicalSpace.Opens ℂ, (U : Set ℂ) ⊆ H → MeasurableSet[ℋ] {ω | Disjoint (C ω) U}) :
    Measurable[ℋ, hittingSigma] fun ω => fillH (cptClosure C ω) :=
  @RetAux79.measurable_fillH_of_dyadic Ω ℋ (cptClosure C) (isDyadicHitMeasurable_cptClosure hCH hC)
    (isCompact_cptClosure C)

end Fill

end InteractingSLE.Theorem14.SB.Lv
