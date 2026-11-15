/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfPm
import InteractingSLE.Spec.Supplement.G7Measurable

/-!
# The forbidden set as a countable union of closed atoms

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). The forbidden set `forb κ θ β` is the union of four
countable families of closed atoms, each selected by a measurable predicate on the word:

* `predR`, `predL`: rational intervals `[a₁, a₂]` free of jump positions where the word is right-bad (right of `0`)
  or left-good (left of `0`, weight `≥ κ/2 − 2`);
* `predJL`, `predJR`: the jump positions left of `0`, and those right of `0` whose right limit is right-bad (read at a
  rational point beyond, with no position in between).

`atom_subset_forb_*` (each atom is forbidden), `exists_atom_of_mem_forb` (every forbidden point is in an atom),
`measurableSet_pred*`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-- The jump positions of `β` avoid `[a, b]`. -/
def PosAvoid (β : BoundaryWord) (a b : ℝ) : Prop := ∀ i < β.1, β.2.1 i < a ∨ b < β.2.1 i

def predR (κ θ : ℝ) (β : BoundaryWord) (a₁ a₂ : ℚ) : Prop :=
  0 < (a₁ : ℝ) ∧ (a₁ : ℝ) < a₂ ∧ PosAvoid β a₁ a₂ ∧ Sec4.cumWeightRight κ (β.fn a₂ + θ * chiC κ) ≤ -2

def predL (κ θ : ℝ) (β : BoundaryWord) (a₁ a₂ : ℚ) : Prop :=
  (a₂ : ℝ) < 0 ∧ (a₁ : ℝ) < a₂ ∧ PosAvoid β a₁ a₂ ∧ κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (β.fn a₁ + θ * chiC κ)

def predJL (β : BoundaryWord) (i : ℕ) : Prop := i < β.1 ∧ β.2.1 i < 0

def predJR (κ θ : ℝ) (β : BoundaryWord) (i : ℕ) : Prop :=
  i < β.1 ∧ 0 < β.2.1 i ∧ ∃ q : ℚ, β.2.1 i < q ∧ (∀ j < β.1, ¬ (β.2.1 i < β.2.1 j ∧ β.2.1 j ≤ q)) ∧
    Sec4.cumWeightRight κ (β.fn q + θ * chiC κ) ≤ -2

/-- A closed rational interval of real points. -/
def atomI (a₁ a₂ : ℚ) : Set ℂ := ((↑) : ℝ → ℂ) '' Icc (a₁ : ℝ) a₂

theorem isClosed_atomI (a₁ a₂ : ℚ) : IsClosed (atomI a₁ a₂) :=
  (isCompact_Icc.image Complex.continuous_ofReal).isClosed

variable {κ θ : ℝ} {β : BoundaryWord}

theorem notMem_jumps_of_posAvoid {a b : ℝ} (h : PosAvoid β a b) {y : ℝ} (hy : y ∈ Icc a b) : y ∉ β.jumps := by
  intro hyJ
  obtain ⟨i, hi, rfl⟩ := BoundaryWord.mem_jumps.1 hyJ
  rcases h i hi with h' | h'
  · exact absurd hy.1 (not_le.2 h')
  · exact absurd hy.2 (not_le.2 h')

/-- **The index is unchanged across a stretch free of positions.** -/
theorem index_eq_of_noPos {s t : ℝ} (hst : s ≤ t) (h : ∀ i < β.1, ¬ (s ≤ β.2.1 i ∧ β.2.1 i < t)) :
    β.index s = β.index t := by
  unfold BoundaryWord.index
  refine congrArg Finset.card (Finset.filter_congr fun i hi => ?_)
  have hi' := Finset.mem_range.1 hi
  constructor
  · intro h1; exact lt_of_lt_of_le h1 hst
  · intro h1
    by_contra h2
    push Not at h2
    exact h i hi' ⟨h2, h1⟩

/-- **The right limit on a stretch free of positions** is the value at its right end. -/
theorem rightLim_eq_of_posAvoid {a b : ℝ} (h : PosAvoid β a b) {y : ℝ} (hy : y ∈ Icc a b) :
    rightLim β.fn y = β.fn b := by
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem β.jumps b
  refine Sec4.rightLim_eq_of_forall (a := b + δ) (by linarith [hy.2]) fun t ht => ?_
  have hnoJ : ∀ i < β.1, ¬ (b < β.2.1 i ∧ β.2.1 i < b + δ) := fun i hi h' =>
    (hδJ _ (BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩)).1 h'
  rcases le_total t b with htb | htb
  · have hidx : β.index t = β.index b := index_eq_of_noPos htb fun i hi h' => by
      rcases h i hi with h1 | h1
      · linarith [hy.1, ht.1, h'.1]
      · linarith [h'.2]
    unfold BoundaryWord.fn
    rw [hidx]
  · have hidx : β.index b = β.index t := index_eq_of_noPos htb fun i hi h' => by
      rcases h i hi with h1 | h1
      · linarith [h'.1, hy.1, hy.2]
      · exact hnoJ i hi ⟨h1, lt_trans h'.2 ht.2⟩
    unfold BoundaryWord.fn
    rw [hidx]

theorem atom_subset_forb_R {a₁ a₂ : ℚ} (h : predR κ θ β a₁ a₂) : atomI a₁ a₂ ⊆ forb κ θ β := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨h0, -, hpos, hw⟩ := h
  refine ⟨by simp, Or.inl ⟨by simp; linarith [hy.1], ?_⟩⟩
  simp only [Complex.ofReal_re]
  rw [rightLim_eq_of_posAvoid hpos hy]
  exact hw

theorem atom_subset_forb_L {a₁ a₂ : ℚ} (h : predL κ θ β a₁ a₂) : atomI a₁ a₂ ⊆ forb κ θ β := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨h0, -, hpos, hw⟩ := h
  refine ⟨by simp, Or.inr ⟨by simp; linarith [hy.2], Or.inr ?_⟩⟩
  simp only [Complex.ofReal_re]
  rw [Supp7.fn_eq_of_positions hpos hy]
  exact hw

theorem mem_forb_JL {i : ℕ} (h : predJL β i) : ((β.2.1 i : ℝ) : ℂ) ∈ forb κ θ β :=
  ⟨by simp, Or.inr ⟨by simpa using h.2, Or.inl (by simpa using BoundaryWord.mem_jumps.2 ⟨i, h.1, rfl⟩)⟩⟩

theorem mem_forb_JR {i : ℕ} (h : predJR κ θ β i) : ((β.2.1 i : ℝ) : ℂ) ∈ forb κ θ β := by
  obtain ⟨hi, hpos, q, hq, hno, hw⟩ := h
  refine ⟨by simp, Or.inl ⟨by simpa using hpos, ?_⟩⟩
  simp only [Complex.ofReal_re]
  have hrl : rightLim β.fn (β.2.1 i) = β.fn q := by
    refine Sec4.rightLim_eq_of_forall (a := q) hq fun t ht => ?_
    have hidx : β.index t = β.index q :=
      index_eq_of_noPos ht.2.le fun j hj hj' => hno j hj ⟨lt_of_lt_of_le ht.1 hj'.1, hj'.2.le⟩
    unfold BoundaryWord.fn
    rw [hidx]
  rw [hrl]
  exact hw

/-- **Every forbidden point lies in an atom.** -/
theorem exists_atom_of_mem_forb {z : ℂ} (hz : z ∈ forb κ θ β) :
    (∃ a₁ a₂ : ℚ, predR κ θ β a₁ a₂ ∧ z ∈ atomI a₁ a₂) ∨ (∃ a₁ a₂ : ℚ, predL κ θ β a₁ a₂ ∧ z ∈ atomI a₁ a₂) ∨
      (∃ i, predJL β i ∧ z = ((β.2.1 i : ℝ) : ℂ)) ∨ (∃ i, predJR κ θ β i ∧ z = ((β.2.1 i : ℝ) : ℂ)) := by
  classical
  obtain ⟨him, hR | ⟨hneg, hJ | hgood⟩⟩ := hz
  · set y := z.re with hy
    have hzy : z = (y : ℂ) := Complex.ext (by simp [hy]) (by simp [him])
    obtain ⟨hpos, hbad⟩ := hR
    obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem β.jumps y
    by_cases hyJ : y ∈ β.jumps
    · -- a jump: read the right limit at a rational point just beyond
      obtain ⟨i, hi, hiy⟩ := BoundaryWord.mem_jumps.1 hyJ
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show y < y + δ by linarith)
      refine Or.inr (Or.inr (Or.inr ⟨i, ⟨hi, by rw [hiy]; exact hpos, q, by rw [hiy]; exact hq1, ?_, ?_⟩, ?_⟩))
      · intro j hj hj'
        have hjJ : β.2.1 j ∈ β.jumps := BoundaryWord.mem_jumps.2 ⟨j, hj, rfl⟩
        rw [hiy] at hj'
        exact (hδJ _ hjJ).1 ⟨hj'.1, lt_of_le_of_lt hj'.2 hq2⟩
      · have hrl : rightLim β.fn y = β.fn q :=
          rightLim_eq_of_gap β.isPiecewiseConstantBoundaryData (fun w hw => (hδJ w hw).1) ⟨hq1, hq2⟩
        rw [← hrl]; exact hbad
      · rw [hzy, hiy]
    · -- not a jump: a jump-free rational interval around it
      have hJ' : ∀ w ∈ β.jumps, w ∉ Ioo (y - δ) (y + δ) := by
        intro w hw hwI
        rcases lt_trichotomy w y with h1 | h1 | h1
        · exact (hδJ w hw).2 ⟨hwI.1, h1⟩
        · exact hyJ (h1 ▸ hw)
        · exact (hδJ w hw).1 ⟨h1, hwI.2⟩
      obtain ⟨a₁, ha₁1, ha₁2⟩ := exists_rat_btwn (show max (y - δ) 0 < y from max_lt (by linarith) hpos)
      obtain ⟨a₂, ha₂1, ha₂2⟩ := exists_rat_btwn (show y < y + δ by linarith)
      have hsub : Icc (a₁ : ℝ) a₂ ⊆ Ioo (y - δ) (y + δ) := fun t ht =>
        ⟨lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) ha₁1) ht.1, lt_of_le_of_lt ht.2 ha₂2⟩
      have hpa : PosAvoid β a₁ a₂ := by
        intro i hi
        by_contra hc
        push Not at hc
        exact hJ' _ (BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩) (hsub hc)
      refine Or.inl ⟨a₁, a₂, ⟨lt_of_le_of_lt (le_max_right _ _) ha₁1, lt_trans ha₁2 ha₂1, hpa, ?_⟩,
        ⟨y, ⟨ha₁2.le, ha₂1.le⟩, hzy.symm⟩⟩
      have hrl := rightLim_eq_of_posAvoid hpa (y := y) ⟨ha₁2.le, ha₂1.le⟩
      rw [← hrl]; exact hbad
  · obtain ⟨i, hi, hiy⟩ := BoundaryWord.mem_jumps.1 hJ
    refine Or.inr (Or.inr (Or.inl ⟨i, ⟨hi, by rw [hiy]; exact hneg⟩, ?_⟩))
    rw [hiy]
    exact Complex.ext (by simp) (by simp [him])
  · set y := z.re with hy
    have hzy : z = (y : ℂ) := Complex.ext (by simp [hy]) (by simp [him])
    by_cases hyJ : y ∈ β.jumps
    · obtain ⟨i, hi, hiy⟩ := BoundaryWord.mem_jumps.1 hyJ
      refine Or.inr (Or.inr (Or.inl ⟨i, ⟨hi, by rw [hiy]; exact hneg⟩, by rw [hzy, hiy]⟩))
    · obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem β.jumps y
      have hJ' : ∀ w ∈ β.jumps, w ∉ Ioo (y - δ) (y + δ) := by
        intro w hw hwI
        rcases lt_trichotomy w y with h1 | h1 | h1
        · exact (hδJ w hw).2 ⟨hwI.1, h1⟩
        · exact hyJ (h1 ▸ hw)
        · exact (hδJ w hw).1 ⟨h1, hwI.2⟩
      obtain ⟨a₁, ha₁1, ha₁2⟩ := exists_rat_btwn (show y - δ < y by linarith)
      obtain ⟨a₂, ha₂1, ha₂2⟩ := exists_rat_btwn (show y < min (y + δ) 0 from lt_min (by linarith) hneg)
      have hsub : Icc (a₁ : ℝ) a₂ ⊆ Ioo (y - δ) (y + δ) := fun t ht =>
        ⟨lt_of_lt_of_le ha₁1 ht.1, lt_of_le_of_lt ht.2 (lt_of_lt_of_le ha₂2 (min_le_left _ _))⟩
      have hpa : PosAvoid β a₁ a₂ := by
        intro i hi
        by_contra hc
        push Not at hc
        exact hJ' _ (BoundaryWord.mem_jumps.2 ⟨i, hi, rfl⟩) (hsub hc)
      refine Or.inr (Or.inl ⟨a₁, a₂, ⟨lt_of_lt_of_le ha₂2 (min_le_right _ _), lt_trans ha₁2 ha₂1, hpa, ?_⟩,
        ⟨y, ⟨ha₁2.le, ha₂1.le⟩, hzy.symm⟩⟩)
      rw [← Supp7.fn_eq_of_positions hpa (y := y) ⟨ha₁2.le, ha₂1.le⟩]
      exact hgood

/-! ### Measurability of the predicates -/

theorem measurable_position (i : ℕ) : Measurable fun c : BoundaryWord => c.2.1 i :=
  (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)

theorem measurableSet_posAvoid (a b : ℝ) : MeasurableSet {c : BoundaryWord | PosAvoid c a b} := by
  have : {c : BoundaryWord | PosAvoid c a b} =
      ⋂ i : ℕ, ({c : BoundaryWord | c.1 ≤ i} ∪ ({c | c.2.1 i < a} ∪ {c | b < c.2.1 i})) := by
    ext c
    simp only [PosAvoid, mem_ofPred_eq, mem_iInter, mem_union]
    refine ⟨fun h i => ?_, fun h i hi => ?_⟩
    · by_cases hi : i < c.1
      · exact Or.inr (h i hi)
      · exact Or.inl (not_lt.1 hi)
    · rcases h i with h' | h'
      · exact absurd hi (not_lt.2 h')
      · exact h'
  rw [this]
  exact MeasurableSet.iInter fun i => (measurable_fst (measurableSet_Iic (a := i))).union
    ((measurableSet_lt (measurable_position i) measurable_const).union
      (measurableSet_lt measurable_const (measurable_position i)))

theorem measurableSet_predR (κ θ : ℝ) (a₁ a₂ : ℚ) : MeasurableSet {c : BoundaryWord | predR κ θ c a₁ a₂} := by
  have hR : Measurable fun c : BoundaryWord => Sec4.cumWeightRight κ (c.fn a₂ + θ * chiC κ) := by
    unfold Sec4.cumWeightRight
    exact (((Supp7.measurable_boundaryWord_fn _).add_const _).div_const _).sub_const _
  have : {c : BoundaryWord | predR κ θ c a₁ a₂} = {_c : BoundaryWord | 0 < (a₁ : ℝ) ∧ (a₁ : ℝ) < a₂} ∩
      ({c | PosAvoid c a₁ a₂} ∩ {c | Sec4.cumWeightRight κ (c.fn a₂ + θ * chiC κ) ≤ -2}) := by
    ext c; simp only [predR, mem_inter_iff, mem_ofPred_eq]; tauto
  rw [this]
  exact (MeasurableSet.const _).inter ((measurableSet_posAvoid _ _).inter (measurableSet_le hR measurable_const))

theorem measurableSet_predL (κ θ : ℝ) (a₁ a₂ : ℚ) : MeasurableSet {c : BoundaryWord | predL κ θ c a₁ a₂} := by
  have hL : Measurable fun c : BoundaryWord => Sec4.cumWeightLeft κ (c.fn a₁ + θ * chiC κ) := by
    unfold Sec4.cumWeightLeft
    exact (((Supp7.measurable_boundaryWord_fn _).add_const _).neg.div_const _).sub_const _
  have : {c : BoundaryWord | predL κ θ c a₁ a₂} = {_c : BoundaryWord | (a₂ : ℝ) < 0 ∧ (a₁ : ℝ) < a₂} ∩
      ({c | PosAvoid c a₁ a₂} ∩ {c | κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (c.fn a₁ + θ * chiC κ)}) := by
    ext c; simp only [predL, mem_inter_iff, mem_ofPred_eq]; tauto
  rw [this]
  exact (MeasurableSet.const _).inter ((measurableSet_posAvoid _ _).inter (measurableSet_le measurable_const hL))

theorem measurableSet_predJL (i : ℕ) : MeasurableSet {c : BoundaryWord | predJL c i} :=
  (measurable_fst (measurableSet_Ioi (a := i))).inter (measurableSet_lt (measurable_position i) measurable_const)

theorem measurableSet_predJR (κ θ : ℝ) (i : ℕ) : MeasurableSet {c : BoundaryWord | predJR κ θ c i} := by
  have hno : ∀ q : ℚ, MeasurableSet {c : BoundaryWord | ∀ j < c.1, ¬ (c.2.1 i < c.2.1 j ∧ c.2.1 j ≤ q)} := by
    intro q
    have : {c : BoundaryWord | ∀ j < c.1, ¬ (c.2.1 i < c.2.1 j ∧ c.2.1 j ≤ q)} =
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
    rw [this]
    exact MeasurableSet.iInter fun j => (measurable_fst (measurableSet_Iic (a := j))).union
      ((measurableSet_le (measurable_position j) (measurable_position i)).union
        (measurableSet_lt measurable_const (measurable_position j)))
  have hR : ∀ q : ℚ, Measurable fun c : BoundaryWord => Sec4.cumWeightRight κ (c.fn q + θ * chiC κ) := by
    intro q
    unfold Sec4.cumWeightRight
    exact (((Supp7.measurable_boundaryWord_fn _).add_const _).div_const _).sub_const _
  have : {c : BoundaryWord | predJR κ θ c i} = {c : BoundaryWord | i < c.1} ∩ ({c | 0 < c.2.1 i} ∩
      ⋃ q : ℚ, ({c | c.2.1 i < q} ∩ ({c | ∀ j < c.1, ¬ (c.2.1 i < c.2.1 j ∧ c.2.1 j ≤ q)} ∩
        {c | Sec4.cumWeightRight κ (c.fn q + θ * chiC κ) ≤ -2}))) := by
    ext c; simp only [predJR, mem_inter_iff, mem_ofPred_eq, mem_iUnion]
  rw [this]
  exact (measurable_fst (measurableSet_Ioi (a := i))).inter
    ((measurableSet_lt measurable_const (measurable_position i)).inter (MeasurableSet.iUnion fun q =>
      (measurableSet_lt (measurable_position i) measurable_const).inter
        ((hno q).inter (measurableSet_le (hR q) measurable_const))))

end InteractingSLE.Theorem14.SB.Wf
