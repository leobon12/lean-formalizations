/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualA15Coupling

/-!
# Zhan's A.1.5: the records of one curve on the limit space are consistent

Packet PROVE-ZHAN-GT4-A15F. Source: Astra, *Follow-up proofs*, §A.1.5 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L417–L420, R38): "Because the augmented marginal laws were fixed, the recorded coordinates are
still the stated Borel functions of the original marginal paths."

On A18's limit space `RecPair` (`exists_dualCoupling_lim`), a curve is represented by its records `x k = (stopped
path at the rational times, stopping time)` for every member `k`. Under each block law the records of all members come
from **one** path, so (`ae_recAgree_of_block`) almost surely under the limit measure, for all members `k, k'` and every
rational time `recTime j` below both stopping times, the two records agree (`RecAgree`); and each record is constant
after its stopping time (`RecStop`, `ae_recStop_of_block`). These are the consistency inputs for reconstructing the two
curves from the records (A18 "What remains" 2(b)).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-- Two records agree at the rational time `recTime j` when it lies below both of their stopping times. -/
def RecAgree (k k' j : ℕ) : Set (ℕ → RecSpace) :=
  {x | ((recTime j : ℝ≥0) : ℝ) ≤ (x k).2 → ((recTime j : ℝ≥0) : ℝ) ≤ (x k').2 → (x k).1 j = (x k').1 j}

/-- A record is constant at rational times after its stopping time. -/
def RecStop (k j j' : ℕ) : Set (ℕ → RecSpace) :=
  {x | (x k).2 ≤ ((recTime j : ℝ≥0) : ℝ) → (x k).2 ≤ ((recTime j' : ℝ≥0) : ℝ) → (x k).1 j = (x k).1 j'}

theorem measurableSet_recAgree (k k' j : ℕ) : MeasurableSet (RecAgree k k' j) := by
  have e : RecAgree k k' j = {x : ℕ → RecSpace | (x k).2 < ((recTime j : ℝ≥0) : ℝ)} ∪
      {x | (x k').2 < ((recTime j : ℝ≥0) : ℝ)} ∪ {x | (x k).1 j = (x k').1 j} := by
    ext x
    simp only [RecAgree, mem_ofPred_eq, mem_union]
    constructor
    · intro h
      by_cases h1 : ((recTime j : ℝ≥0) : ℝ) ≤ (x k).2
      · by_cases h2 : ((recTime j : ℝ≥0) : ℝ) ≤ (x k').2
        · exact Or.inr (h h1 h2)
        · exact Or.inl (Or.inr (not_le.1 h2))
      · exact Or.inl (Or.inl (not_le.1 h1))
    · rintro ((h | h) | h) h1 h2
      · exact absurd h1 (not_le.2 h)
      · exact absurd h2 (not_le.2 h)
      · exact h
  have hk : Measurable fun x : ℕ → RecSpace => x k := measurable_pi_apply k
  have hk' : Measurable fun x : ℕ → RecSpace => x k' := measurable_pi_apply k'
  rw [e]
  refine ((measurableSet_lt (measurable_snd.comp hk) measurable_const).union
    (measurableSet_lt (measurable_snd.comp hk') measurable_const)).union ?_
  exact measurableSet_eq_fun ((measurable_pi_apply j).comp (measurable_fst.comp hk))
    ((measurable_pi_apply j).comp (measurable_fst.comp hk'))

theorem measurableSet_recStop (k j j' : ℕ) : MeasurableSet (RecStop k j j') := by
  have e : RecStop k j j' = {x : ℕ → RecSpace | ((recTime j : ℝ≥0) : ℝ) < (x k).2} ∪
      {x | ((recTime j' : ℝ≥0) : ℝ) < (x k).2} ∪ {x | (x k).1 j = (x k).1 j'} := by
    ext x
    simp only [RecStop, mem_ofPred_eq, mem_union]
    constructor
    · intro h
      by_cases h1 : (x k).2 ≤ ((recTime j : ℝ≥0) : ℝ)
      · by_cases h2 : (x k).2 ≤ ((recTime j' : ℝ≥0) : ℝ)
        · exact Or.inr (h h1 h2)
        · exact Or.inl (Or.inr (not_le.1 h2))
      · exact Or.inl (Or.inl (not_le.1 h1))
    · rintro ((h | h) | h) h1 h2
      · exact absurd h1 (not_le.2 h)
      · exact absurd h2 (not_le.2 h)
      · exact h
  have hk : Measurable fun x : ℕ → RecSpace => x k := measurable_pi_apply k
  rw [e]
  refine ((measurableSet_lt measurable_const (measurable_snd.comp hk)).union
    (measurableSet_lt measurable_const (measurable_snd.comp hk))).union ?_
  exact measurableSet_eq_fun ((measurable_pi_apply j).comp (measurable_fst.comp hk))
    ((measurable_pi_apply j').comp (measurable_fst.comp hk))

section Path

variable {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (S : ℕ → Ω → ℝ≥0) (ω : Ω)

/-- The records of all members of one path agree below both stopping times. -/
theorem recAll_mem_recAgree (k k' j : ℕ) : recAll B S ω ∈ RecAgree k k' j := by
  intro h1 h2
  simp only [recAll, recPath] at h1 h2 ⊢
  rw [min_eq_left (NNReal.coe_le_coe.1 h1), min_eq_left (NNReal.coe_le_coe.1 h2)]

/-- The record of one path is constant after its stopping time. -/
theorem recAll_mem_recStop (k j j' : ℕ) : recAll B S ω ∈ RecStop k j j' := by
  intro h1 h2
  simp only [recAll, recPath] at h1 h2 ⊢
  rw [min_eq_right (NNReal.coe_le_coe.1 h1), min_eq_right (NNReal.coe_le_coe.1 h2)]

end Path

theorem truncRec_apply_of_le {K k : ℕ} (hk : k ≤ K) (x : ℕ → RecSpace) : truncRec K x k = x k := by
  simp only [truncRec, hk, ite_true]

/-- A push-forward of a measure by an a.e.-measurable map with values in a measurable set `A` does not charge `Aᶜ`. -/
theorem map_compl_eq_zero_of_forall_mem {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {ν : Measure α}
    {f : α → β} (hm : AEMeasurable f ν) {A : Set β} (hA : MeasurableSet A) (hf : ∀ a, f a ∈ A) :
    ν.map f Aᶜ = 0 := by
  rw [Measure.map_apply_of_aemeasurable hm hA.compl]
  have : f ⁻¹' Aᶜ = ∅ := eq_empty_of_forall_notMem fun a ha => ha (hf a)
  rw [this, measure_empty]

/-- If every block of a coordinate `g : RecPair → ℕ → RecSpace` has the law of the corresponding block of the records
of one path, then almost surely every finite-block property satisfied by all such records holds. -/
theorem ae_mem_of_block {α : Type*} [MeasurableSpace α] {μ : Measure RecPair} {ν : ℕ → Measure α}
    {g : RecPair → ℕ → RecSpace} (hg : Measurable g) {R : α → ℕ → RecSpace} (hRm : Measurable R)
    (hblock : ∀ K, μ.map (fun z => truncRec K (g z)) = (ν K).map fun a => truncRec K (R a))
    {A : Set (ℕ → RecSpace)} (hA : MeasurableSet A) {K : ℕ}
    (htr : ∀ x, truncRec K x ∈ A ↔ x ∈ A) (hR : ∀ a, R a ∈ A) : ∀ᵐ z ∂μ, g z ∈ A := by
  have hmeas : Measurable fun z => truncRec K (g z) := (continuous_truncRec K).measurable.comp hg
  rw [ae_iff]
  have e : {z | ¬ g z ∈ A} = (fun z => truncRec K (g z)) ⁻¹' Aᶜ := by
    ext z
    simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff, htr]
  rw [e, ← Measure.map_apply hmeas hA.compl, hblock K]
  exact map_compl_eq_zero_of_forall_mem ((continuous_truncRec K).measurable.comp hRm).aemeasurable hA
    fun a => (htr _).2 (hR a)

/-- **Consistency of the records**: under block laws of the records of one path, almost surely all records agree
below both stopping times and are constant after their stopping times. -/
theorem ae_recAgree_of_block {α : Type*} [MeasurableSpace α] {μ : Measure RecPair} {ν : ℕ → Measure α}
    {g : RecPair → ℕ → RecSpace} (hg : Measurable g) {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {S : ℕ → Ω → ℝ≥0}
    {π : α → Ω} (hRm : Measurable fun a => recAll B S (π a))
    (hblock : ∀ K, μ.map (fun z => truncRec K (g z)) = (ν K).map fun a => truncRec K (recAll B S (π a))) :
    ∀ᵐ z ∂μ, (∀ k k' j, g z ∈ RecAgree k k' j) ∧ ∀ k j j', g z ∈ RecStop k j j' := by
  refine (ae_all_iff.2 fun k => ae_all_iff.2 fun k' => ae_all_iff.2 fun j => ?_).and
    (ae_all_iff.2 fun k => ae_all_iff.2 fun j => ae_all_iff.2 fun j' => ?_)
  · refine ae_mem_of_block hg hRm hblock (measurableSet_recAgree k k' j) (K := max k k') (fun x => ?_)
      fun a => recAll_mem_recAgree B S (π a) k k' j
    simp only [RecAgree, mem_ofPred_eq, truncRec_apply_of_le (le_max_left k k'),
      truncRec_apply_of_le (le_max_right k k')]
  · refine ae_mem_of_block hg hRm hblock (measurableSet_recStop k j j') (K := k) (fun x => ?_)
      fun a => recAll_mem_recStop B S (π a) k j j'
    simp only [RecStop, mem_ofPred_eq, truncRec_apply_of_le (le_refl k)]

end InteractingSLE.ZhanGT4
