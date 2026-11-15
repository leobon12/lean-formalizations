import InteractingSLE.Spec.Coupling.ResampleChain

/-!
# Order statistics of finitely many stopping times (Theorem 1.1, obligation 3)

Packet PROVE-T11-KER (Astra p. 5: "Sort the pairs lexicographically by `(τ_i, i)` and call the ordered times
`σ_1 ≤ ⋯ ≤ σ_N`. Let `V_j` be the union of the sets whose constraints have not yet been discharged"). For finitely
many stopping times `τ i`, `ordStat τ k` is the `k`-th smallest value (`ordStat τ 0 = 0`, and the maximum beyond the
number of times); it is a stopping time, nondecreasing in `k`, and every `τ i` is one of them
(`exists_ordStat_eq`). The region indices are `stageSet τ 0 = stageSet τ 1 = univ` and
`stageSet τ (k + 2) = {j | ordStat τ (k + 1) < τ j}` (the pairs not discharged by stage `k + 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

section OrderStat

variable {Ω : Type*} {ι : Type*} [Fintype ι]

theorem powersetCard_min_nonempty (k : ℕ) :
    (Finset.univ.powersetCard (min k (Fintype.card ι)) : Finset (Finset ι)).Nonempty :=
  Finset.powersetCard_nonempty.2 (by rw [Finset.card_univ]; exact min_le_right _ _)

/-- The `k`-th order statistic of the values `τ i ω` (`0` for `k = 0`, the maximum for `k ≥ card ι`). -/
def ordStat (τ : ι → Ω → ℝ≥0) (k : ℕ) (ω : Ω) : ℝ≥0 :=
  (Finset.univ.powersetCard (min k (Fintype.card ι))).inf' (powersetCard_min_nonempty k)
    fun S => S.sup fun i => τ i ω

variable {τ : ι → Ω → ℝ≥0}

theorem ordStat_le_iff (k : ℕ) (ω : Ω) (t : ℝ≥0) :
    ordStat τ k ω ≤ t ↔ ∃ S : Finset ι, S.card = min k (Fintype.card ι) ∧ ∀ i ∈ S, τ i ω ≤ t := by
  simp only [ordStat, Finset.inf'_le_iff, Finset.mem_powersetCard, Finset.subset_univ, true_and,
    Finset.sup_le_iff]

theorem ordStat_zero (ω : Ω) : ordStat τ 0 ω = 0 :=
  le_antisymm ((ordStat_le_iff 0 ω 0).2 ⟨∅, by simp, by simp⟩) (zero_le (a := ordStat τ 0 ω))

theorem ordStat_mono {k k' : ℕ} (h : k ≤ k') (ω : Ω) : ordStat τ k ω ≤ ordStat τ k' ω := by
  obtain ⟨S', hS', hS'eq⟩ := Finset.exists_mem_eq_inf' (powersetCard_min_nonempty (ι := ι) k')
    fun S => S.sup fun i => τ i ω
  rw [Finset.mem_powersetCard] at hS'
  obtain ⟨S, hSS', hS⟩ := Finset.exists_subset_card_eq (s := S')
    (n := min k (Fintype.card ι)) (by rw [hS'.2]; exact min_le_min h le_rfl)
  rw [ordStat, ordStat, hS'eq]
  refine (Finset.inf'_le _ (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS⟩)).trans ?_
  exact Finset.sup_mono hSS'

theorem ordStat_le_of_mem (i : ι) (ω : Ω) (hN : 1 ≤ Fintype.card ι) :
    ordStat τ 1 ω ≤ τ i ω := by
  refine (ordStat_le_iff 1 ω _).2 ⟨{i}, ?_, by simp⟩
  rw [Finset.card_singleton, min_eq_left hN]

/-- An unvisited time is above the next order statistic. -/
theorem ordStat_succ_le_of_lt [DecidableEq ι] {k : ℕ} {i : ι} {ω : Ω} (h : ordStat τ k ω < τ i ω) :
    ordStat τ (k + 1) ω ≤ τ i ω := by
  obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_inf' (powersetCard_min_nonempty (ι := ι) k)
    fun S => S.sup fun i => τ i ω
  rw [Finset.mem_powersetCard] at hS
  have hle : ∀ j ∈ S, τ j ω < τ i ω := fun j hj => by
    refine lt_of_le_of_lt ?_ h
    rw [ordStat, hSeq]
    exact Finset.le_sup (f := fun i => τ i ω) hj
  have hiS : i ∉ S := fun hi => lt_irrefl _ (hle i hi)
  have hkN : k < Fintype.card ι := by
    by_contra hk
    push Not at hk
    have : S = Finset.univ := Finset.eq_univ_of_card S (by rw [hS.2, min_eq_right hk])
    exact hiS (this ▸ Finset.mem_univ i)
  refine (ordStat_le_iff (k + 1) ω _).2 ⟨insert i S, ?_, fun j hj => ?_⟩
  · rw [Finset.card_insert_of_notMem hiS, hS.2, min_eq_left hkN.le, min_eq_left hkN]
  · rcases Finset.mem_insert.1 hj with rfl | hj
    · exact le_rfl
    · exact (hle j hj).le

/-- **Every time is an order statistic, at a stage where it is not yet discharged**: for
`k = #{j | τ j < τ i} + 1`, `ordStat τ k = τ i`, and `τ i` exceeds `ordStat τ (k - 1)` unless `k = 1`. -/
theorem exists_ordStat_eq (i : ι) (ω : Ω) :
    ∃ m : ℕ, m + 1 ≤ Fintype.card ι ∧ ordStat τ (m + 1) ω = τ i ω ∧ (m = 0 ∨ ordStat τ m ω < τ i ω) := by
  classical
  set L : Finset ι := Finset.univ.filter fun j => τ j ω < τ i ω with hL
  set m := L.card with hm
  have hiL : i ∉ L := by simp [hL]
  have hm1 : m + 1 ≤ Fintype.card ι := by
    rw [hm, ← Finset.card_insert_of_notMem hiL]; exact Finset.card_le_univ _
  refine ⟨m, hm1, le_antisymm ?_ ?_, ?_⟩
  · refine (ordStat_le_iff (m + 1) ω _).2 ⟨insert i L, ?_, fun j hj => ?_⟩
    · rw [Finset.card_insert_of_notMem hiL, min_eq_left hm1]
    · rcases Finset.mem_insert.1 hj with rfl | hj
      · exact le_rfl
      · exact (Finset.mem_filter.1 hj).2.le
  · by_contra hlt
    push Not at hlt
    obtain ⟨S, hS, hSle⟩ := (ordStat_le_iff (τ := τ) (m + 1) ω (ordStat τ (m + 1) ω)).1 le_rfl
    have hSL : S ⊆ L := fun j hj => Finset.mem_filter.2 ⟨Finset.mem_univ j, (hSle j hj).trans_lt hlt⟩
    have := Finset.card_le_card hSL
    rw [hS, min_eq_left hm1] at this
    omega
  · rcases Nat.eq_zero_or_pos m with h0 | hpos
    · exact Or.inl h0
    · refine Or.inr (lt_of_le_of_lt ((ordStat_le_iff m ω (L.sup fun j => τ j ω)).2
        ⟨L, (min_eq_left (by omega)).symm, fun j hj => Finset.le_sup (f := fun j => τ j ω) hj⟩) ?_)
      obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup L (Finset.card_pos.1 hpos) fun j => τ j ω
      rw [hjeq]
      exact (Finset.mem_filter.1 hj).2

variable {mΩ : MeasurableSpace Ω} {𝓖 : MeasureTheory.Filtration ℝ≥0 mΩ}

theorem isStoppingTime_ordStat (hτ : ∀ i, IsStoppingTime 𝓖 fun ω => (τ i ω : WithTop ℝ≥0)) (k : ℕ) :
    IsStoppingTime 𝓖 fun ω => (ordStat τ k ω : WithTop ℝ≥0) := by
  intro t
  have : {ω | (ordStat τ k ω : WithTop ℝ≥0) ≤ t} =
      ⋃ S ∈ (Finset.univ.powersetCard (min k (Fintype.card ι)) : Finset (Finset ι)),
        ⋂ i ∈ S, {ω | (τ i ω : WithTop ℝ≥0) ≤ t} := by
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe, ordStat_le_iff, mem_iUnion, mem_iInter,
      Finset.mem_powersetCard, Finset.subset_univ, true_and, exists_prop]
  rw [this]
  exact Finset.measurableSet_biUnion _ fun S _ => Finset.measurableSet_biInter _ fun i _ => hτ i t

/-- The stage regions: all pairs at stages `0` and `1`, then the pairs not discharged by the previous stage. -/
def stageSet (τ : ι → Ω → ℝ≥0) : ℕ → Ω → Finset ι
  | 0 => fun _ => Finset.univ
  | 1 => fun _ => Finset.univ
  | k + 2 => fun ω => Finset.univ.filter fun j => ordStat τ (k + 1) ω < τ j ω

theorem stageSet_succ_subset (k : ℕ) (ω : Ω) : stageSet τ (k + 1) ω ⊆ stageSet τ k ω := by
  rcases k with _ | _ | k
  · exact Finset.subset_univ _
  · exact Finset.subset_univ _
  · intro j hj
    simp only [stageSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact lt_of_le_of_lt (ordStat_mono (Nat.le_succ _) ω) hj

/-- A pair in the stage region is protected through the stage time. -/
theorem ordStat_le_of_mem_stageSet [DecidableEq ι] {k : ℕ} (hk : 1 ≤ k) {j : ι} {ω : Ω} (hj : j ∈ stageSet τ k ω) :
    ordStat τ k ω ≤ τ j ω := by
  rcases k with _ | _ | k
  · omega
  · exact ordStat_le_of_mem j ω (Fintype.card_pos_iff.2 ⟨j⟩)
  · simp only [stageSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ordStat_succ_le_of_lt hj

end OrderStat

end Coupling

end InteractingSLE
