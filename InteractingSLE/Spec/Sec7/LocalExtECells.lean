/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtEStop

/-!
# The cells of the restart rule: fixed seed pattern, dyadic radius and integer part of the stopping time

Packet PROVE-LOCEXT-E. Lemma 7.5's proof, p. 252: "The finitely many possible amalgamated seed-weight pairs and countably
many chosen radii supply a measurable restart rule".

A cell code `c = (N, S_L, S_R, k)` fixes the integer part `N` of the stopping time, the seed pattern (the marks at the
driver, `S_L`, `S_R`) of the current state and the dyadic seed radius `2^{-k}` of the current positions (the least
admissible one, so that the cells are disjoint).

* `posL`, `posR`: the positions of a state relative to its driver;
* `IsCellState c x`: the state `x` has the seed pattern and the least admissible dyadic radius of `c`;
  `measurableSet_isCellState`;
* `cellSet c`: the recorded histories `y` with `N ≤ τ_y < N + 1` whose current state is a cell state;
  `measurableSet_cellSet`;
* `IsAdmCode c`: the seed weights of the pattern are `> −2`; at an admissible cell state the threshold condition
  fails (`not_thresholdCondition_of_isCellState`); every state at which it fails is a cell state of some admissible
  code (`exists_isCellState`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec7

variable {nL nR : ℕ}

/-! ### Cell codes and cell states -/

/-- The positions of the left marks of a state relative to its driver. -/
def posL (x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : Fin nL → ℝ := fun i => x.2.1 i - x.1

/-- The positions of the right marks of a state relative to its driver. -/
def posR (x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : Fin nR → ℝ := fun j => x.2.2 j - x.1

theorem measurable_posL : Measurable (posL (nL := nL) (nR := nR)) :=
  Measurable.of_eval fun i => ((measurable_pi_apply i).comp measurable_snd.fst).sub measurable_fst

theorem measurable_posR : Measurable (posR (nL := nL) (nR := nR)) :=
  Measurable.of_eval fun j => ((measurable_pi_apply j).comp measurable_snd.snd).sub measurable_fst

/-- Cell codes `(N, S_L, S_R, k)`. -/
abbrev CellCode (nL nR : ℕ) : Type := ℕ × Finset (Fin nL) × Finset (Fin nR) × ℕ

/-- The radius `2^{-k}` of a cell code. -/
def CellCode.radius (c : CellCode nL nR) : ℝ := (1 / 2 : ℝ) ^ c.2.2.2

theorem CellCode.radius_pos (c : CellCode nL nR) : 0 < c.radius := by
  unfold CellCode.radius; positivity

/-- **A cell state of the code `c = (N, S_L, S_R, k)`**: the marks at the driver are exactly `S_L`, `S_R`, and `2^{-k}`
is the largest admissible dyadic seed radius of the positions. -/
def IsCellState (c : CellCode nL nR) (x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : Prop :=
  (∀ i, x.2.1 i = x.1 ↔ i ∈ c.2.1) ∧ (∀ j, x.2.2 j = x.1 ↔ j ∈ c.2.2.1) ∧
    IsSeedRadius (posL x) (posR x) ((1 / 2 : ℝ) ^ c.2.2.2) ∧
    ∀ m < c.2.2.2, ¬ IsSeedRadius (posL x) (posR x) ((1 / 2 : ℝ) ^ m)

theorem measurableSet_isSeedRadius (ρ : ℝ) :
    MeasurableSet {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | IsSeedRadius (posL x) (posR x) ρ} := by
  have e : {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | IsSeedRadius (posL x) (posR x) ρ} =
      {_x | 0 < ρ} ∩ (⋂ i, ({x | posL x i = 0} ∪ {x | 8 * ρ < |posL x i|})) ∩
        ⋂ j, ({x | posR x j = 0} ∪ {x | 8 * ρ < |posR x j|}) := by
    ext x
    simp only [IsSeedRadius, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, or_iff_not_imp_left]
    tauto
  rw [e]
  have hL : ∀ i, Measurable fun x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => posL x i := fun i =>
    (measurable_pi_apply i).comp measurable_posL
  have hR : ∀ j, Measurable fun x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) => posR x j := fun j =>
    (measurable_pi_apply j).comp measurable_posR
  refine ((MeasurableSet.const _).inter (MeasurableSet.iInter fun i => ?_)).inter (MeasurableSet.iInter fun j => ?_)
  · exact (measurableSet_eq_fun (hL i) measurable_const).union
      (measurableSet_lt measurable_const (hL i).abs)
  · exact (measurableSet_eq_fun (hR j) measurable_const).union
      (measurableSet_lt measurable_const (hR j).abs)

theorem measurableSet_isCellState (c : CellCode nL nR) :
    MeasurableSet {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | IsCellState c x} := by
  have e : {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | IsCellState c x} =
      (⋂ i, {x | x.2.1 i = x.1 ↔ i ∈ c.2.1}) ∩ (⋂ j, {x | x.2.2 j = x.1 ↔ j ∈ c.2.2.1}) ∩
        {x | IsSeedRadius (posL x) (posR x) ((1 / 2 : ℝ) ^ c.2.2.2)} ∩
        ⋂ m ∈ Finset.range c.2.2.2, {x | IsSeedRadius (posL x) (posR x) ((1 / 2 : ℝ) ^ m)}ᶜ := by
    ext x
    simp only [IsCellState, mem_ofPred_eq, mem_inter_iff, mem_iInter, Finset.mem_range, mem_compl_iff]
    tauto
  rw [e]
  have hiff : ∀ {s : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (p : Prop), MeasurableSet s →
      MeasurableSet {x | x ∈ s ↔ p} := by
    intro s p hs
    by_cases hp : p
    · have e : {x | x ∈ s ↔ p} = s := by ext x; simp only [hp, iff_true, mem_ofPred_eq]
      rw [e]; exact hs
    · have e : {x | x ∈ s ↔ p} = sᶜ := by ext x; simp only [hp, iff_false, mem_ofPred_eq, mem_compl_iff]
      rw [e]; exact hs.compl
  refine (((MeasurableSet.iInter fun i => ?_).inter (MeasurableSet.iInter fun j => ?_)).inter
    (measurableSet_isSeedRadius _)).inter
    (MeasurableSet.biInter (Finset.range _).countable_toSet fun m _ => (measurableSet_isSeedRadius _).compl)
  · exact hiff (s := {x | x.2.1 i = x.1}) _
      (measurableSet_eq_fun ((measurable_pi_apply i).comp measurable_snd.fst) measurable_fst)
  · exact hiff (s := {x | x.2.2 j = x.1}) _
      (measurableSet_eq_fun ((measurable_pi_apply j).comp measurable_snd.snd) measurable_fst)

/-- **The cell of a code**: the recorded histories `y` with `N ≤ τ_y < N + 1` whose current state is a cell state. -/
def cellSet (c : CellCode nL nR) : Set (DrivingHist nL nR) :=
  {y | ((c.1 : ℝ≥0) : WithTop ℝ≥0) ≤ y.1 ∧ y.1 < (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) ∧
    IsCellState c (histState y)}

theorem measurableSet_cellSet (c : CellCode nL nR) : MeasurableSet (cellSet c) := by
  have e : cellSet c = Prod.fst ⁻¹' Ici (((c.1 : ℝ≥0) : WithTop ℝ≥0)) ∩
      Prod.fst ⁻¹' Iio (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) ∩ histState ⁻¹' {x | IsCellState c x} := by
    ext y; simp only [cellSet, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Ici, mem_Iio, and_assoc]
  rw [e]
  exact ((measurable_fst measurableSet_Ici).inter (measurable_fst measurableSet_Iio)).inter
    (measurable_histState (measurableSet_isCellState c))

/-! ### Admissible codes -/

/-- An admissible code: the seed weights of its pattern are `> −2`. -/
def IsAdmCode (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (c : CellCode nL nR) : Prop :=
  -2 < ∑ i ∈ c.2.1, ρL i ∧ -2 < ∑ j ∈ c.2.2.1, ρR j

theorem filter_eq_left_of_isCellState {c : CellCode nL nR} {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hx : IsCellState c x) : Finset.univ.filter (fun i => x.2.1 i = x.1) = c.2.1 := by
  ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx.1 i]

theorem filter_eq_right_of_isCellState {c : CellCode nL nR} {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hx : IsCellState c x) : Finset.univ.filter (fun j => x.2.2 j = x.1) = c.2.2.1 := by
  ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hx.2.1 j]

/-- At a cell state of an admissible code the threshold condition fails. -/
theorem not_thresholdCondition_of_isCellState {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {c : CellCode nL nR}
    (hc : IsAdmCode ρL ρR c) {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (hx : IsCellState c x) :
    ¬ ForceWord.ThresholdCondition ρL ρR x.1 x.2.1 x.2.2 := by
  unfold ForceWord.ThresholdCondition
  rw [filter_eq_left_of_isCellState hx, filter_eq_right_of_isCellState hx, not_or, not_le, not_le]
  exact hc

/-- **Every admissible state is a cell state of an admissible code** with any prescribed integer part. -/
theorem exists_isCellState {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (N : ℕ) {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)}
    (hx : ¬ ForceWord.ThresholdCondition ρL ρR x.1 x.2.1 x.2.2) :
    ∃ c : CellCode nL nR, c.1 = N ∧ IsAdmCode ρL ρR c ∧ IsCellState c x := by
  classical
  have hk := exists_isSeedRadius_half_pow (posL x) (posR x)
  refine ⟨(N, Finset.univ.filter (fun i => x.2.1 i = x.1), Finset.univ.filter (fun j => x.2.2 j = x.1),
    Nat.find hk), rfl, ?_, ?_⟩
  · unfold ForceWord.ThresholdCondition at hx
    rw [not_or, not_le, not_le] at hx
    exact hx
  · refine ⟨fun i => ?_, fun j => ?_, Nat.find_spec hk, fun m hm => Nat.find_min hk hm⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Cell states of two codes with the same integer part are cell states of the same code. -/
theorem eq_of_isCellState {c c' : CellCode nL nR} {x : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (hN : c.1 = c'.1)
    (hc : IsCellState c x) (hc' : IsCellState c' x) : c = c' := by
  obtain ⟨N, SL, SR, k⟩ := c
  obtain ⟨N', SL', SR', k'⟩ := c'
  have hSL : SL = SL' := (filter_eq_left_of_isCellState hc).symm.trans (filter_eq_left_of_isCellState hc')
  have hSR : SR = SR' := (filter_eq_right_of_isCellState hc).symm.trans (filter_eq_right_of_isCellState hc')
  have hk : k = k' := by
    rcases lt_trichotomy k k' with h | h | h
    · exact absurd hc.2.2.1 (hc'.2.2.2 k h)
    · exact h
    · exact absurd hc'.2.2.1 (hc.2.2.2 k' h)
  simp only at hN
  rw [hN, hSL, hSR, hk]

end LocalExt

end InteractingSLE
