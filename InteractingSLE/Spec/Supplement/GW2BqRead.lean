/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BqCell

/-!
# The near exit cell read from the record

Packet PROVE-GW2-BUF (round 14). The cell `(K, R, k)` of the near exit is read from the stage record `y`.

* The shape `K = shape y` (D16's decoder).
* The radius `R = n + 1 + ⌈Σ |posL y i| + Σ |posR y j|⌉`.
* The least level index `k` with `(1/2)^k ≤ 1/(n+1)` and `(1/2)^k` below every controlled initial gap.

The controlled labels are those of `cellBuf`: left `i ≥ mL` and right `j ≥ nR − 1` in the upper orientation, left
`i ≥ nL − 1` and right `j ≥ mR` in the lower one.

* **`measurable_cellOf`** (for measurable shape and position readers).
* **`cellOf_spec`**: suppose the record's shape and labels are those of a near crossing family `f`. Then
  * the cell buffer contains `nearBuffer f n`, and
  * it contains the initial comparison state `(0, f.xL, f.xR)`, by the family's orientation clause: the controlled
    gaps are positive.
* **`imgState_zero`**: the image state at time `0` of a path from `0` is `(0, xL, xR)` for signed labels.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId GW2TipSystem GW2TipSystem.RootN4 GW2JDetR11 Supp12.DSReach
  MartChar.RealFlow

/-- The controlled left labels of a shape (as in `cellBuf`). -/
def ctrlL (K : NearShape) (i : ℕ) : Prop := if K.2.2.2.2 then K.2.2.1 ≤ i else K.1 - 1 ≤ i

/-- The controlled right labels of a shape (as in `cellBuf`). -/
def ctrlR (K : NearShape) (j : ℕ) : Prop := if K.2.2.2.2 then K.2.1 - 1 ≤ j else K.2.2.2.1 ≤ j

section Read

variable (n : ℕ) (shape : RecData → NearShape) (posL posR : RecData → ℕ → ℝ)

/-- The box radius of the record's cell. -/
def radOf (y : RecData) : ℕ :=
  n + 1 + ⌈∑ i ∈ Finset.range (shape y).1, |posL y i| + ∑ j ∈ Finset.range (shape y).2.1, |posR y j|⌉₊

/-- An admissible level index: below `1/(n+1)` and below every controlled initial gap. -/
def LevOK (k : ℕ) (y : RecData) : Prop :=
  (1 / 2 : ℝ) ^ k ≤ 1 / ((n : ℝ) + 1) ∧ (∀ i < (shape y).1, ctrlL (shape y) i → (1 / 2 : ℝ) ^ k < -posL y i) ∧
    ∀ j < (shape y).2.1, ctrlR (shape y) j → (1 / 2 : ℝ) ^ k < posR y j

open Classical in
/-- The least admissible level index (`0` if none). -/
def levOf (y : RecData) : ℕ := if h : ∃ k, LevOK n shape posL posR k y then Nat.find h else 0

/-- **The near exit cell of the record.** -/
def cellOf (y : RecData) : NearCell := (shape y, radOf n shape posL posR y, levOf n shape posL posR y)

variable {shape posL posR}

theorem measurable_sum_range {N : RecData → ℕ} (hN : Measurable N) {g : RecData → ℕ → ℝ} (hg : Measurable g) :
    Measurable fun y => ∑ i ∈ Finset.range (N y), g y i := by
  have h : Measurable fun q : RecData × ℕ => ∑ i ∈ Finset.range q.2, g q.1 i :=
    measurable_from_prod_countable_left fun m => by
      show Measurable fun x => ∑ i ∈ Finset.range m, g x i
      exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp hg
  exact h.comp (measurable_id.prodMk hN)

theorem measurable_radOf (hsh : Measurable shape) (hL : Measurable posL) (hR : Measurable posR) :
    Measurable (radOf n shape posL posR) := by
  have h1 : Measurable fun y => (shape y).1 := measurable_fst.comp hsh
  have h2 : Measurable fun y => (shape y).2.1 := measurable_fst.comp (measurable_snd.comp hsh)
  have hA : Measurable fun y => |posL y| := measurable_pi_iff.2 fun i => ((measurable_pi_apply i).comp hL).abs
  have hB : Measurable fun y => |posR y| := measurable_pi_iff.2 fun j => ((measurable_pi_apply j).comp hR).abs
  have hs := (measurable_sum_range h1 hA).add (measurable_sum_range h2 hB)
  exact measurable_const.add (Nat.measurable_ceil.comp hs)

theorem measurableSet_levOK (hsh : Measurable shape) (hL : Measurable posL) (hR : Measurable posR) (k : ℕ) :
    MeasurableSet {y | LevOK n shape posL posR k y} := by
  have hc : ∀ (P : NearShape → Prop), MeasurableSet {y | P (shape y)} := fun P =>
    hsh (Set.to_countable {K : NearShape | P K}).measurableSet
  have h1 : Measurable fun y => (shape y).1 := measurable_fst.comp hsh
  have h2 : Measurable fun y => (shape y).2.1 := measurable_fst.comp (measurable_snd.comp hsh)
  have hlt : ∀ (N : RecData → ℕ), Measurable N → ∀ i : ℕ, MeasurableSet {y | i < N y} := fun N hN i =>
    hN (MeasurableSet.of_discrete (s := {m : ℕ | i < m}))
  have eL : {y | ∀ i < (shape y).1, ctrlL (shape y) i → (1 / 2 : ℝ) ^ k < -posL y i} =
      ⋂ i : ℕ, ({y | i < (shape y).1}ᶜ ∪ ({y | ctrlL (shape y) i}ᶜ ∪ {y | (1 / 2 : ℝ) ^ k < -posL y i})) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    exact forall_congr' fun i => by tauto
  have eR : {y | ∀ j < (shape y).2.1, ctrlR (shape y) j → (1 / 2 : ℝ) ^ k < posR y j} =
      ⋂ j : ℕ, ({y | j < (shape y).2.1}ᶜ ∪ ({y | ctrlR (shape y) j}ᶜ ∪ {y | (1 / 2 : ℝ) ^ k < posR y j})) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    exact forall_congr' fun j => by tauto
  have e : {y | LevOK n shape posL posR k y} = {y : RecData | (1 / 2 : ℝ) ^ k ≤ 1 / ((n : ℝ) + 1)} ∩
      ({y | ∀ i < (shape y).1, ctrlL (shape y) i → (1 / 2 : ℝ) ^ k < -posL y i} ∩
        {y | ∀ j < (shape y).2.1, ctrlR (shape y) j → (1 / 2 : ℝ) ^ k < posR y j}) := by
    ext y
    simp only [LevOK, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [e, eL, eR]
  refine (MeasurableSet.const _).inter ((MeasurableSet.iInter fun i => ?_).inter (MeasurableSet.iInter fun j => ?_))
  · have hneg : Measurable fun y => -posL y i := by exact ((measurable_pi_apply i).comp hL).neg
    exact (hlt _ h1 i).compl.union ((hc (fun K => ctrlL K i)).compl.union (measurableSet_lt measurable_const hneg))
  · have hpos : Measurable fun y => posR y j := by exact (measurable_pi_apply j).comp hR
    exact (hlt _ h2 j).compl.union ((hc (fun K => ctrlR K j)).compl.union (measurableSet_lt measurable_const hpos))

theorem measurable_levOf (hsh : Measurable shape) (hL : Measurable posL) (hR : Measurable posR) :
    Measurable (levOf n shape posL posR) := by
  classical
  refine measurable_to_countable' fun k => ?_
  have hok := measurableSet_levOK n hsh hL hR
  have e : levOf n shape posL posR ⁻¹' {k} =
      ({y | LevOK n shape posL posR k y} ∩ ⋂ j : Fin k, {y | LevOK n shape posL posR j y}ᶜ) ∪
        ((⋂ j : ℕ, {y | LevOK n shape posL posR j y}ᶜ) ∩ {_y | k = 0}) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, levOf, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_iInter, Set.mem_compl_iff]
    by_cases h : ∃ j, LevOK n shape posL posR j y
    · simp only [h, ↓reduceDIte]
      rw [Nat.find_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact Or.inl ⟨h1, fun j => h2 j j.2⟩
      · rintro (⟨h1, h2⟩ | ⟨h3, -⟩)
        · exact ⟨h1, fun j hj => h2 ⟨j, hj⟩⟩
        · exact absurd h (fun ⟨j, hj⟩ => h3 j hj)
    · simp only [h, ↓reduceDIte]
      simp only [not_exists] at h
      constructor
      · intro hk
        exact Or.inr ⟨h, hk.symm⟩
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact absurd h1 (h k)
        · exact h2.symm
  rw [e]
  exact ((hok k).inter (MeasurableSet.iInter fun j : Fin k => (hok (j : ℕ)).compl)).union
    ((MeasurableSet.iInter fun j : ℕ => (hok j).compl).inter (MeasurableSet.const _))

theorem measurable_cellOf (hsh : Measurable shape) (hL : Measurable posL) (hR : Measurable posR) :
    Measurable (cellOf n shape posL posR) :=
  hsh.prodMk ((measurable_radOf n hsh hL hR).prodMk (measurable_levOf n hsh hL hR))

end Read

/-! ### The near family's cell -/

/-- **The image state at time `0`** of a path from `0`, with signed labels. -/
theorem imgState_zero {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {w : ℝ≥0 → ℝ} (hw0 : w 0 = 0) : GW2Sdg.imgState xL xR w 0 = (0, xL, xR) := by
  have hf : frozenDrive w ((0 : ℝ≥0) : ℝ) = fun _ => 0 := by
    funext s
    simp only [frozenDrive, NNReal.coe_zero]
    have : (min s 0).toNNReal = 0 := Real.toNNReal_of_nonpos (min_le_right _ _)
    rw [this, hw0]
  unfold GW2Sdg.imgState
  rw [hf]
  have hc : Continuous fun _ : ℝ => (0 : ℝ) := continuous_const
  have hc' : Continuous fun s : ℝ => -(fun _ : ℝ => (0 : ℝ)) s := continuous_const.neg
  refine Prod.ext hw0 (Prod.ext (funext fun i => ?_) (funext fun j => ?_))
  · show -rightImg (fun s => -(fun _ : ℝ => (0 : ℝ)) s) (-xL i) ((0 : ℝ≥0) : ℝ) = xL i
    rw [NNReal.coe_zero, rightImg_zero hc' (by simp) (neg_nonneg.2 (hxL i)), neg_neg]
  · show rightImg (fun _ : ℝ => (0 : ℝ)) (xR j) ((0 : ℝ≥0) : ℝ) = xR j
    rw [NNReal.coe_zero, rightImg_zero hc rfl (hxR j)]

end InteractingSLE.Theorem14.GW2Bh
