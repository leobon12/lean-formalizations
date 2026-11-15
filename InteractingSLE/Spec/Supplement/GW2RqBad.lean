/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqAvoid
import InteractingSLE.Spec.Supplement.SB2WfPs

/-!
# Visits of the avoided set, read at rational times (decision D33)

PROVE-GW2-ROOTX round 8. To move "the trace never visits `avoidQ κ θ β`" between a kernel and the ambient law, the
event must be measurable. As for SB2WORD's `BadVisit`, `avoidQ` is covered by countably many closed atoms whose
selection is a measurable predicate of the word:

* `atomRQ`, `atomLQ`: closed rational intervals without positions and of cumulative weight `≥ κ/2 − 2`;
  `jumpRQ`, `jumpLQ`: positions whose weight beyond them (read at a rational point) is `> κ/2 − 4`;
* `BadQ κ θ β Γ T`: some atom is visited before `T` (`SB.Wf.visitBefore`, rational times);
* **`subset_avoidQ_of_badQ`**: a bad visit of a continuous path visits `avoidQ`; **`badQ_of_mem_avoidQ`**: a visit of
  `avoidQ` before `T` is a bad visit;
* **`measurableSet_badQ`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rq

open Restart Exist Exist.StagedLaw SB.Wf
open PiecewiseConstantBoundaryData (jumpSet leftLim rightLim)

variable (κ θ : ℝ) (β : BoundaryWord)

/-- A right closed rational atom: no positions, cumulative weight `≥ κ/2 − 2`. -/
def atomRQ (a₁ a₂ : ℚ) : Prop :=
  0 < (a₁ : ℝ) ∧ (a₁ : ℝ) < a₂ ∧ PosAvoid β a₁ a₂ ∧ κ / 2 - 2 ≤ Sec4.cumWeightRight κ (β.fn a₂ + θ * chiC κ)

/-- A left closed rational atom. -/
def atomLQ (a₁ a₂ : ℚ) : Prop :=
  (a₂ : ℝ) < 0 ∧ (a₁ : ℝ) < a₂ ∧ PosAvoid β a₁ a₂ ∧ κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (β.fn a₁ + θ * chiC κ)

/-- A positive position with weight beyond it `> κ/2 − 4`, read at a rational point right of it. -/
def jumpRQ (i : ℕ) : Prop :=
  i < β.1 ∧ 0 < β.2.1 i ∧ ∃ q : ℚ, β.2.1 i < q ∧ (∀ j < β.1, ¬ (β.2.1 i < β.2.1 j ∧ β.2.1 j ≤ q)) ∧
    κ / 2 - 4 < Sec4.cumWeightRight κ (β.fn q + θ * chiC κ)

/-- A negative position with weight beyond it `> κ/2 − 4`, read at a rational point left of it. -/
def jumpLQ (i : ℕ) : Prop :=
  i < β.1 ∧ β.2.1 i < 0 ∧ ∃ q : ℚ, (q : ℝ) < β.2.1 i ∧ (∀ j < β.1, ¬ ((q : ℝ) ≤ β.2.1 j ∧ β.2.1 j < β.2.1 i)) ∧
    κ / 2 - 4 < Sec4.cumWeightLeft κ (β.fn q + θ * chiC κ)

/-- **Some atom of the avoided set is visited before `T`** (rational reading). -/
def BadQ (Γ : ℝ≥0 → ℂ) (T : ℝ≥0∞) : Prop :=
  (∃ a₁ a₂ : ℚ, atomRQ κ θ β a₁ a₂ ∧ visitBefore Γ T (atomI a₁ a₂)) ∨
    (∃ a₁ a₂ : ℚ, atomLQ κ θ β a₁ a₂ ∧ visitBefore Γ T (atomI a₁ a₂)) ∨
    (∃ i, jumpRQ κ θ β i ∧ visitBefore Γ T {((β.2.1 i : ℝ) : ℂ)}) ∨
    (∃ i, jumpLQ κ θ β i ∧ visitBefore Γ T {((β.2.1 i : ℝ) : ℂ)})

variable {κ θ β}

/-! ### Constancy between positions -/

theorem fn_eq_of_posAvoid {a b : ℝ} (h : PosAvoid β a b) {y y' : ℝ} (hy : y ∈ Icc a b) (hy' : y' ∈ Icc a b) :
    β.fn y = β.fn y' := by
  have e : β.index y = β.index y' := by
    unfold BoundaryWord.index
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    refine and_congr_right fun hi => ?_
    rcases h i hi with h' | h'
    · exact ⟨fun _ => h'.trans_le hy'.1, fun _ => h'.trans_le hy.1⟩
    · exact ⟨fun h'' => absurd (h''.trans_le hy.2) (not_lt.2 h'.le), fun h'' => absurd (h''.trans_le hy'.2)
        (not_lt.2 h'.le)⟩
  unfold BoundaryWord.fn
  rw [e]

theorem fn_eq_of_noPos_right {z q : ℝ} (hno : ∀ j < β.1, ¬ (z < β.2.1 j ∧ β.2.1 j ≤ q)) {t : ℝ}
    (ht : t ∈ Ioo z q) : β.fn t = β.fn q := by
  have e : β.index t = β.index q := by
    unfold BoundaryWord.index
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    refine and_congr_right fun hj => ?_
    constructor
    · intro h'; exact h'.trans ht.2
    · intro h'
      by_contra h''
      exact hno j hj ⟨ht.1.trans_le (not_lt.1 h''), h'.le⟩
  unfold BoundaryWord.fn
  rw [e]

theorem fn_eq_of_noPos_left {z q : ℝ} (hno : ∀ j < β.1, ¬ (q ≤ β.2.1 j ∧ β.2.1 j < z)) {t : ℝ}
    (ht : t ∈ Ioo q z) : β.fn t = β.fn q := by
  have e : β.index t = β.index q := by
    unfold BoundaryWord.index
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    refine and_congr_right fun hj => ?_
    constructor
    · intro h'
      by_contra h''
      exact hno j hj ⟨not_lt.1 h'', h'.trans ht.2⟩
    · intro h'; exact h'.trans ht.1
  unfold BoundaryWord.fn
  rw [e]

/-! ### Atoms lie in the avoided set -/

theorem atomI_subset_avoidQ_R {a₁ a₂ : ℚ} (h : atomRQ κ θ β a₁ a₂) : atomI a₁ a₂ ⊆ avoidQ κ θ β := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨by simp, Or.inl ⟨by simpa using h.1.trans_le hy.1, Or.inl ⟨by simpa using notMem_jumps_of_posAvoid h.2.2.1 hy,
    ?_⟩⟩⟩
  simp only [Complex.ofReal_re]
  rw [fn_eq_of_posAvoid h.2.2.1 hy ⟨h.2.1.le, le_rfl⟩]
  exact h.2.2.2

theorem atomI_subset_avoidQ_L {a₁ a₂ : ℚ} (h : atomLQ κ θ β a₁ a₂) : atomI a₁ a₂ ⊆ avoidQ κ θ β := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨by simp, Or.inr ⟨by simpa using hy.2.trans_lt h.1, Or.inl ⟨by simpa using notMem_jumps_of_posAvoid h.2.2.1 hy,
    ?_⟩⟩⟩
  simp only [Complex.ofReal_re]
  rw [fn_eq_of_posAvoid h.2.2.1 hy ⟨le_rfl, h.2.1.le⟩]
  exact h.2.2.2

theorem mem_avoidQ_of_jumpRQ {i : ℕ} (h : jumpRQ κ θ β i) : ((β.2.1 i : ℝ) : ℂ) ∈ avoidQ κ θ β := by
  obtain ⟨hi, hpos, q, hq, hno, hc⟩ := h
  refine ⟨by simp, Or.inl ⟨by simpa using hpos, Or.inr ⟨by simpa using BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩, ?_⟩⟩⟩
  simp only [Complex.ofReal_re]
  rw [Sec4.rightLim_eq_of_forall hq fun t ht => fn_eq_of_noPos_right hno ht]
  exact hc

theorem mem_avoidQ_of_jumpLQ {i : ℕ} (h : jumpLQ κ θ β i) : ((β.2.1 i : ℝ) : ℂ) ∈ avoidQ κ θ β := by
  obtain ⟨hi, hneg, q, hq, hno, hc⟩ := h
  refine ⟨by simp, Or.inr ⟨by simpa using hneg, Or.inr ⟨by simpa using BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩, ?_⟩⟩⟩
  simp only [Complex.ofReal_re]
  rw [Sec4.leftLim_eq_of_forall hq fun t ht => fn_eq_of_noPos_left hno ht]
  exact hc

/-! ### Bad visits are visits of the avoided set, and conversely -/

/-- **A bad visit of a continuous path visits the avoided set.** -/
theorem exists_mem_avoidQ_of_badQ {Γ : ℝ≥0 → ℂ} {T : ℝ≥0∞} (hΓ : ContinuousOn Γ {t | (t : ℝ≥0∞) < T})
    (hb : BadQ κ θ β Γ T) : ∃ t : ℝ≥0, (t : ℝ≥0∞) < T ∧ Γ t ∈ avoidQ κ θ β := by
  rcases hb with ⟨a₁, a₂, ha, hv⟩ | ⟨a₁, a₂, ha, hv⟩ | ⟨i, hi, hv⟩ | ⟨i, hi, hv⟩
  · obtain ⟨t, ht, hm⟩ := (visitBefore_iff hΓ (isClosed_atomI a₁ a₂) (atomI_nonempty ha.2.1)).1 hv
    exact ⟨t, ht, atomI_subset_avoidQ_R ha hm⟩
  · obtain ⟨t, ht, hm⟩ := (visitBefore_iff hΓ (isClosed_atomI a₁ a₂) (atomI_nonempty ha.2.1)).1 hv
    exact ⟨t, ht, atomI_subset_avoidQ_L ha hm⟩
  · obtain ⟨t, ht, hm⟩ := (visitBefore_iff hΓ isClosed_singleton (singleton_nonempty _)).1 hv
    rw [mem_singleton_iff] at hm
    exact ⟨t, ht, hm ▸ mem_avoidQ_of_jumpRQ hi⟩
  · obtain ⟨t, ht, hm⟩ := (visitBefore_iff hΓ isClosed_singleton (singleton_nonempty _)).1 hv
    rw [mem_singleton_iff] at hm
    exact ⟨t, ht, hm ▸ mem_avoidQ_of_jumpLQ hi⟩

/-- **A visit of the avoided set before `T` is a bad visit.** -/
theorem badQ_of_mem_avoidQ {Γ : ℝ≥0 → ℂ} {T : ℝ≥0∞} (hΓ : ContinuousOn Γ {t | (t : ℝ≥0∞) < T}) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < T) (hm : Γ t ∈ avoidQ κ θ β) : BadQ κ θ β Γ T := by
  obtain ⟨him, hR | hL⟩ := hm
  · set z := (Γ t).re with hz
    have hze : Γ t = (z : ℂ) := Complex.ext (by simp [hz]) (by simp [him])
    obtain ⟨hpos, ⟨hzJ, hc⟩ | ⟨hzJ, hc⟩⟩ := hR
    · obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem β.jumps z
      obtain ⟨a₁, ha₁, ha₁z⟩ := exists_rat_btwn (show max (z - δ) 0 < z from max_lt (by linarith) hpos)
      obtain ⟨a₂, hza₂, ha₂⟩ := exists_rat_btwn (show z < z + δ by linarith)
      have hpa : PosAvoid β a₁ a₂ := by
        intro i hi
        have hmem : β.2.1 i ∈ β.jumps := BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩
        by_contra hc'
        push Not at hc'
        rcases lt_trichotomy (β.2.1 i) z with h1 | h1 | h1
        · exact (hδJ _ hmem).2 ⟨by linarith [le_max_left (z - δ) 0], h1⟩
        · exact hzJ (h1 ▸ hmem)
        · exact (hδJ _ hmem).1 ⟨h1, by linarith⟩
      have ha : atomRQ κ θ β a₁ a₂ := ⟨lt_of_le_of_lt (le_max_right _ _) ha₁, ha₁z.trans hza₂, hpa, by
        rw [fn_eq_of_posAvoid hpa ⟨by exact_mod_cast hza₂.le.trans' ha₁z.le, le_rfl⟩ ⟨ha₁z.le, hza₂.le⟩]
        exact hc⟩
      exact Or.inl ⟨a₁, a₂, ha, (visitBefore_iff hΓ (isClosed_atomI a₁ a₂) (atomI_nonempty ha.2.1)).2
        ⟨t, ht, ⟨z, ⟨ha₁z.le, hza₂.le⟩, hze.symm⟩⟩⟩
    · obtain ⟨i, hi, hiz⟩ := BoundaryWord.mem_jumps.1 hzJ
      obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem β.jumps z
      obtain ⟨q, hzq, hq⟩ := exists_rat_btwn (show z < z + δ by linarith)
      have hno : ∀ j < β.1, ¬ (β.2.1 i < β.2.1 j ∧ β.2.1 j ≤ q) := by
        intro j hj ⟨h1, h2⟩
        rw [hiz] at h1
        exact (hδJ _ (BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩)).1 ⟨h1, by linarith⟩
      have hrl : rightLim β.fn z = β.fn q := by
        rw [← hiz]
        exact Sec4.rightLim_eq_of_forall (by rw [hiz]; exact_mod_cast hzq) fun t' ht' =>
          fn_eq_of_noPos_right hno ht'
      have hj : jumpRQ κ θ β i := ⟨hi, by rw [hiz]; exact hpos, q, by rw [hiz]; exact_mod_cast hzq, hno, by
        rw [← hrl]; exact hc⟩
      refine Or.inr (Or.inr (Or.inl ⟨i, hj, (visitBefore_iff hΓ isClosed_singleton (singleton_nonempty _)).2
        ⟨t, ht, ?_⟩⟩))
      rw [mem_singleton_iff, hze, hiz]
  · set z := (Γ t).re with hz
    have hze : Γ t = (z : ℂ) := Complex.ext (by simp [hz]) (by simp [him])
    obtain ⟨hneg, ⟨hzJ, hc⟩ | ⟨hzJ, hc⟩⟩ := hL
    · obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem β.jumps z
      obtain ⟨a₁, ha₁, ha₁z⟩ := exists_rat_btwn (show z - δ < z by linarith)
      obtain ⟨a₂, hza₂, ha₂⟩ := exists_rat_btwn (show z < min (z + δ) 0 from lt_min (by linarith) hneg)
      have hpa : PosAvoid β a₁ a₂ := by
        intro i hi
        have hmem : β.2.1 i ∈ β.jumps := BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩
        by_contra hc'
        push Not at hc'
        rcases lt_trichotomy (β.2.1 i) z with h1 | h1 | h1
        · exact (hδJ _ hmem).2 ⟨by linarith, h1⟩
        · exact hzJ (h1 ▸ hmem)
        · exact (hδJ _ hmem).1 ⟨h1, by linarith [min_le_left (z + δ) 0]⟩
      have ha : atomLQ κ θ β a₁ a₂ := ⟨lt_of_lt_of_le ha₂ (min_le_right _ _), ha₁z.trans hza₂, hpa, by
        rw [fn_eq_of_posAvoid hpa ⟨le_rfl, ha₁z.le.trans hza₂.le⟩ ⟨ha₁z.le, hza₂.le⟩]
        exact hc⟩
      exact Or.inr (Or.inl ⟨a₁, a₂, ha, (visitBefore_iff hΓ (isClosed_atomI a₁ a₂) (atomI_nonempty ha.2.1)).2
        ⟨t, ht, ⟨z, ⟨ha₁z.le, hza₂.le⟩, hze.symm⟩⟩⟩)
    · obtain ⟨i, hi, hiz⟩ := BoundaryWord.mem_jumps.1 hzJ
      obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem β.jumps z
      obtain ⟨q, hq, hqz⟩ := exists_rat_btwn (show z - δ < z by linarith)
      have hno : ∀ j < β.1, ¬ ((q : ℝ) ≤ β.2.1 j ∧ β.2.1 j < β.2.1 i) := by
        intro j hj ⟨h1, h2⟩
        rw [hiz] at h2
        exact (hδJ _ (BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩)).2 ⟨by linarith, h2⟩
      have hll : leftLim β.fn z = β.fn q := by
        rw [← hiz]
        exact Sec4.leftLim_eq_of_forall (by rw [hiz]; exact_mod_cast hqz) fun t' ht' =>
          fn_eq_of_noPos_left hno ht'
      have hj : jumpLQ κ θ β i := ⟨hi, by rw [hiz]; exact hneg, q, by rw [hiz]; exact_mod_cast hqz, hno, by
        rw [← hll]; exact hc⟩
      refine Or.inr (Or.inr (Or.inr ⟨i, hj, (visitBefore_iff hΓ isClosed_singleton (singleton_nonempty _)).2
        ⟨t, ht, ?_⟩⟩))
      rw [mem_singleton_iff, hze, hiz]

/-! ### Measurability -/

theorem measurable_cumR (q : ℝ) : Measurable fun c : BoundaryWord => Sec4.cumWeightRight κ (c.fn q + θ * chiC κ) := by
  unfold Sec4.cumWeightRight
  exact (((Supp7.measurable_boundaryWord_fn _).add_const _).div_const _).sub_const _

theorem measurable_cumL (q : ℝ) : Measurable fun c : BoundaryWord => Sec4.cumWeightLeft κ (c.fn q + θ * chiC κ) := by
  unfold Sec4.cumWeightLeft
  exact ((((Supp7.measurable_boundaryWord_fn _).add_const _).neg.div_const _).sub_const _)

variable (κ θ) in
theorem measurableSet_atomRQ (a₁ a₂ : ℚ) : MeasurableSet {c : BoundaryWord | atomRQ κ θ c a₁ a₂} := by
  have e : {c : BoundaryWord | atomRQ κ θ c a₁ a₂} = {_c : BoundaryWord | 0 < (a₁ : ℝ)} ∩
      ({_c : BoundaryWord | (a₁ : ℝ) < a₂} ∩ ({c : BoundaryWord | PosAvoid c a₁ a₂} ∩
        {c : BoundaryWord | κ / 2 - 2 ≤ Sec4.cumWeightRight κ (c.fn a₂ + θ * chiC κ)})) := by
    ext c; simp only [atomRQ, mem_inter_iff, mem_ofPred_eq]
  rw [e]
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter ((measurableSet_posAvoid _ _).inter
    (measurableSet_le measurable_const (measurable_cumR (κ := κ) (θ := θ) _))))

variable (κ θ) in
theorem measurableSet_atomLQ (a₁ a₂ : ℚ) : MeasurableSet {c : BoundaryWord | atomLQ κ θ c a₁ a₂} := by
  have e : {c : BoundaryWord | atomLQ κ θ c a₁ a₂} = {_c : BoundaryWord | (a₂ : ℝ) < 0} ∩
      ({_c : BoundaryWord | (a₁ : ℝ) < a₂} ∩ ({c : BoundaryWord | PosAvoid c a₁ a₂} ∩
        {c : BoundaryWord | κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (c.fn a₁ + θ * chiC κ)})) := by
    ext c; simp only [atomLQ, mem_inter_iff, mem_ofPred_eq]
  rw [e]
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter ((measurableSet_posAvoid _ _).inter
    (measurableSet_le measurable_const (measurable_cumL (κ := κ) (θ := θ) _))))

theorem measurableSet_lt_card (i : ℕ) : MeasurableSet {c : BoundaryWord | i < c.1} :=
  measurable_fst (measurableSet_Ioi (a := i))

variable (κ θ) in
theorem measurableSet_jumpRQ (i : ℕ) : MeasurableSet {c : BoundaryWord | jumpRQ κ θ c i} := by
  have hno : ∀ q : ℚ, MeasurableSet {c : BoundaryWord | ∀ j < c.1, ¬ (c.2.1 i < c.2.1 j ∧ c.2.1 j ≤ q)} := by
    intro q
    have e : {c : BoundaryWord | ∀ j < c.1, ¬ (c.2.1 i < c.2.1 j ∧ c.2.1 j ≤ q)} =
        ⋂ j : ℕ, ({c : BoundaryWord | c.1 ≤ j} ∪ ({c | c.2.1 j ≤ c.2.1 i} ∪ {c | (q : ℝ) < c.2.1 j})) := by
      ext c
      simp only [mem_ofPred_eq, mem_iInter, mem_union, not_and, not_le]
      refine ⟨fun h j => ?_, fun h j hj h1 => ?_⟩
      · by_cases hj : j < c.1
        · by_cases h1 : c.2.1 i < c.2.1 j
          · exact Or.inr (Or.inr (h j hj h1))
          · exact Or.inr (Or.inl (not_lt.1 h1))
        · exact Or.inl (not_lt.1 hj)
      · rcases h j with h' | h' | h'
        · exact absurd hj (not_lt.2 h')
        · exact absurd h1 (not_lt.2 h')
        · exact h'
    rw [e]
    exact MeasurableSet.iInter fun j => (measurable_fst (measurableSet_Iic (a := j))).union
      ((measurableSet_le (measurable_position j) (measurable_position i)).union
        (measurableSet_lt measurable_const (measurable_position j)))
  have e : {c : BoundaryWord | jumpRQ κ θ c i} = {c : BoundaryWord | i < c.1} ∩ ({c | 0 < c.2.1 i} ∩
      ⋃ q : ℚ, ({c : BoundaryWord | c.2.1 i < q} ∩ ({c | ∀ j < c.1, ¬ (c.2.1 i < c.2.1 j ∧ c.2.1 j ≤ q)} ∩
        {c | κ / 2 - 4 < Sec4.cumWeightRight κ (c.fn q + θ * chiC κ)}))) := by
    ext c
    simp only [jumpRQ, mem_ofPred_eq, mem_inter_iff, mem_iUnion]
  rw [e]
  exact (measurableSet_lt_card i).inter ((measurableSet_lt measurable_const (measurable_position i)).inter
    (MeasurableSet.iUnion fun q => (measurableSet_lt (measurable_position i) measurable_const).inter
      ((hno q).inter (measurableSet_lt measurable_const (measurable_cumR (κ := κ) (θ := θ) _)))))

variable (κ θ) in
theorem measurableSet_jumpLQ (i : ℕ) : MeasurableSet {c : BoundaryWord | jumpLQ κ θ c i} := by
  have hno : ∀ q : ℚ, MeasurableSet {c : BoundaryWord | ∀ j < c.1, ¬ ((q : ℝ) ≤ c.2.1 j ∧ c.2.1 j < c.2.1 i)} := by
    intro q
    have e : {c : BoundaryWord | ∀ j < c.1, ¬ ((q : ℝ) ≤ c.2.1 j ∧ c.2.1 j < c.2.1 i)} =
        ⋂ j : ℕ, ({c : BoundaryWord | c.1 ≤ j} ∪ ({c | c.2.1 j < q} ∪ {c | c.2.1 i ≤ c.2.1 j})) := by
      ext c
      simp only [mem_ofPred_eq, mem_iInter, mem_union, not_and, not_lt]
      refine ⟨fun h j => ?_, fun h j hj h1 => ?_⟩
      · by_cases hj : j < c.1
        · by_cases h1 : (q : ℝ) ≤ c.2.1 j
          · exact Or.inr (Or.inr (h j hj h1))
          · exact Or.inr (Or.inl (not_le.1 h1))
        · exact Or.inl (not_lt.1 hj)
      · rcases h j with h' | h' | h'
        · exact absurd hj (not_lt.2 h')
        · exact absurd h1 (not_le.2 h')
        · exact h'
    rw [e]
    exact MeasurableSet.iInter fun j => (measurable_fst (measurableSet_Iic (a := j))).union
      ((measurableSet_lt (measurable_position j) measurable_const).union
        (measurableSet_le (measurable_position i) (measurable_position j)))
  have e : {c : BoundaryWord | jumpLQ κ θ c i} = {c : BoundaryWord | i < c.1} ∩ ({c | c.2.1 i < 0} ∩
      ⋃ q : ℚ, ({c : BoundaryWord | (q : ℝ) < c.2.1 i} ∩
        ({c | ∀ j < c.1, ¬ ((q : ℝ) ≤ c.2.1 j ∧ c.2.1 j < c.2.1 i)} ∩
          {c | κ / 2 - 4 < Sec4.cumWeightLeft κ (c.fn q + θ * chiC κ)}))) := by
    ext c
    simp only [jumpLQ, mem_ofPred_eq, mem_inter_iff, mem_iUnion]
  rw [e]
  exact (measurableSet_lt_card i).inter ((measurableSet_lt (measurable_position i) measurable_const).inter
    (MeasurableSet.iUnion fun q => (measurableSet_lt measurable_const (measurable_position i)).inter
      ((hno q).inter (measurableSet_lt measurable_const (measurable_cumL (κ := κ) (θ := θ) _)))))

variable (κ θ) in
/-- **Bad visits are measurable.** -/
theorem measurableSet_badQ {Ω : Type*} [MeasurableSpace Ω] {b : Ω → BoundaryWord} (hb : Measurable b)
    {Γ : Ω → ℝ≥0 → ℂ} (hΓ : ∀ q : ℝ≥0, Measurable fun ω => Γ ω q) {T : Ω → ℝ≥0∞} (hT : Measurable T) :
    MeasurableSet {ω | BadQ κ θ (b ω) (Γ ω) (T ω)} := by
  have hpos : ∀ i : ℕ, Measurable fun ω => (((b ω).2.1 i : ℝ) : ℂ) := fun i =>
    Complex.measurable_ofReal.comp ((measurable_position i).comp hb)
  have e : {ω | BadQ κ θ (b ω) (Γ ω) (T ω)} =
      (⋃ a₁ : ℚ, ⋃ a₂ : ℚ, (b ⁻¹' {c | atomRQ κ θ c a₁ a₂} ∩ {ω | visitBefore (Γ ω) (T ω) (atomI a₁ a₂)})) ∪
      ((⋃ a₁ : ℚ, ⋃ a₂ : ℚ, (b ⁻¹' {c | atomLQ κ θ c a₁ a₂} ∩ {ω | visitBefore (Γ ω) (T ω) (atomI a₁ a₂)})) ∪
      ((⋃ i : ℕ, (b ⁻¹' {c | jumpRQ κ θ c i} ∩ {ω | visitBefore (Γ ω) (T ω) {(((b ω).2.1 i : ℝ) : ℂ)}})) ∪
      (⋃ i : ℕ, (b ⁻¹' {c | jumpLQ κ θ c i} ∩ {ω | visitBefore (Γ ω) (T ω) {(((b ω).2.1 i : ℝ) : ℂ)}})))) := by
    ext ω
    simp only [BadQ, mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, mem_preimage]
  rw [e]
  refine MeasurableSet.union (MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
    (hb (measurableSet_atomRQ κ θ a₁ a₂)).inter (measurableSet_visitBefore hΓ hT _))
    (MeasurableSet.union (MeasurableSet.iUnion fun a₁ => MeasurableSet.iUnion fun a₂ =>
      (hb (measurableSet_atomLQ κ θ a₁ a₂)).inter (measurableSet_visitBefore hΓ hT _))
      (MeasurableSet.union (MeasurableSet.iUnion fun i =>
        (hb (measurableSet_jumpRQ κ θ i)).inter (measurableSet_visitBefore_pt hΓ hT (hpos i)))
        (MeasurableSet.iUnion fun i =>
          (hb (measurableSet_jumpLQ κ θ i)).inter (measurableSet_visitBefore_pt hΓ hT (hpos i)))))

end InteractingSLE.Theorem14.GW2Rq
