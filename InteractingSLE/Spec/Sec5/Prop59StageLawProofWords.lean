/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageCross

/-!
# Proposition 5.9's stage words: the conditions `hwL`, `hwR` from the initial word

Packet PROVE-PROP59T3. Specification §5.2, proof of Proposition 5.9 (`source/spec/p097-144.md` L1006–L1016,
`p145-192.md` L50–L62, pp. 144–146): "At angle `+π/2`, the far boundary heights in Figure 5.8 are `−λ′ + 3πχ/2` and
`λ′ − πχ/2`. […] their total left and right weights are `κ − 4` and `c = κ/2 − 2`"; "the force points associated with
the previous flow-line pieces cannot be hit before that endpoint: their cumulative weights satisfy the
non-boundary-intersection inequalities"; the angle-change weights are `ρ^{i,R} = (χ/λ)(θ_{j−i+1} − θ_{j−i})`,
`ρ^{i,L} = −ρ^{i,R}` (`stageρL`, `stageρR`).

PROVE-PROP59T2's experiment (`ae_not_isBounded_of_stageLaw`) takes the deterministic word conditions

* `hwL : ∀ j, Even j → IsStageWordN κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)` (leftward stages),
* `hwR : ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ ρR₀ j) (stageρL κ ρL₀ j)` (rightward stages, reflected).

This file reduces both to conditions on the initial word (`IsStageInit`): with `M = πχ/λ = 2 − κ/2`, the new weights
alternate `∓M`, so their partial sums lie in `{0, ∓M}` and their totals are `0` after an even and `±M` after an odd
number of switches. Hence the conditions at every depth are those at depths `0` and `1`:

* left total `κ − 4`, right total `κ/2 − 2`;
* left proper prefix sums `≥ κ/2 − 2` (depth 0) — then every left prefix sum is `≥ κ − 4` (depth 1);
* right proper prefix sums `≥ 0` (depth 1) — then every right prefix sum is `≥ κ/2 − 2` (depth 0).

Conversely the two depth-`0`/`1` conditions imply `IsStageInit` (`isStageInit_of_hw`), so `IsStageInit` is exactly
the content of `hwL ∧ hwR`.

## Main results

* `psum`: prefix sums of a finite word (the sums of `Sec4.Cond44`); `psum_consAlt`;
* `isStageWordN_of_psum`, `IsStageWordN.psum`: `IsStageWordN` in prefix-sum form;
* `IsStageInit`; **`hwL_of_isStageInit`**, **`hwR_of_isStageInit`**; **`isStageInit_of_hw`**.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace InteractingSLE

namespace Sec5

namespace Prop59Stage

/-! ### Prefix sums -/

section Psum

/-- **The prefix sum** of the first `m` weights of a finite word (the sums of `Sec4.Cond44`). -/
def psum {n : ℕ} (ρ : Fin n → ℝ) (m : ℕ) : ℝ := ∑ i ∈ univ.filter (fun i : Fin n => i.val < m), ρ i

theorem psum_eq_sum_ite {n : ℕ} (ρ : Fin n → ℝ) (m : ℕ) :
    psum ρ m = ∑ i : Fin n, if i.val < m then ρ i else 0 := by
  rw [psum, sum_filter]

@[simp] theorem psum_zero {n : ℕ} (ρ : Fin n → ℝ) : psum ρ 0 = 0 := by
  simp only [psum_eq_sum_ite, Nat.not_lt_zero, ↓reduceIte, sum_const_zero]

theorem psum_of_le {n : ℕ} (ρ : Fin n → ℝ) {m : ℕ} (hm : n ≤ m) : psum ρ m = ∑ i, ρ i := by
  rw [psum_eq_sum_ite]
  exact sum_congr rfl fun i _ => by simp only [lt_of_lt_of_le i.2 hm, ↓reduceIte]

theorem psum_cons_succ {n : ℕ} (a : ℝ) (ρ : Fin n → ℝ) (m : ℕ) :
    psum (Fin.cons a ρ : Fin (n + 1) → ℝ) (m + 1) = a + psum ρ m := by
  rw [psum_eq_sum_ite, psum_eq_sum_ite, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte, Fin.cons_zero, Fin.val_succ, Fin.cons_succ,
    Nat.add_lt_add_iff_right]

theorem psum_snoc_of_le {n : ℕ} (ρ : Fin n → ℝ) (a : ℝ) {m : ℕ} (hm : m ≤ n) :
    psum (Fin.snoc ρ a : Fin (n + 1) → ℝ) m = psum ρ m := by
  rw [psum_eq_sum_ite, psum_eq_sum_ite, Fin.sum_univ_castSucc]
  have hl : ¬ (Fin.last n).val < m := by simp only [Fin.val_last, not_lt]; exact hm
  simp only [Fin.val_castSucc, Fin.snoc_castSucc, hl, ↓reduceIte, add_zero]

theorem psum_snoc_succ {n : ℕ} (ρ : Fin n → ℝ) (a : ℝ) :
    psum (Fin.snoc ρ a : Fin (n + 1) → ℝ) (n + 1) = (∑ i, ρ i) + a := by
  rw [psum_of_le _ le_rfl, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The sum over `Finset.Iic j` is the prefix sum of length `j + 1`. -/
theorem sum_Iic_eq_psum {n : ℕ} (ρ : Fin n → ℝ) (j : Fin n) : ∑ i ∈ Iic j, ρ i = psum ρ (j.val + 1) := by
  rw [psum]
  refine sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_Iic, mem_filter, mem_univ, true_and, Fin.le_iff_val_le_val, Nat.lt_succ_iff]

/-- The sum of the initial word over `Finset.Iic j` is the prefix sum of length `j + 1` of the whole word. -/
theorem sum_Iic_init_eq_psum {m : ℕ} (ρ : Fin (m + 1) → ℝ) (j : Fin m) :
    ∑ i ∈ Iic j, Fin.init ρ i = psum ρ (j.val + 1) := by
  rw [sum_Iic_eq_psum, psum_eq_sum_ite, psum_eq_sum_ite, Fin.sum_univ_castSucc]
  have hl : ¬ (Fin.last m).val < j.val + 1 := by simp only [Fin.val_last, not_lt]; exact j.2
  simp only [Fin.init, Fin.val_castSucc, hl, ↓reduceIte, add_zero]

/-- **The prefix sums of a prepended word**: the first `min m j` new weights and the first `m − j` initial ones. -/
theorem psum_consAlt (c : ℕ → ℝ) {n₀ : ℕ} (ρ₀ : Fin n₀ → ℝ) (j m : ℕ) :
    psum (consAlt c ρ₀ j) m = (∑ i ∈ range (min m j), c (j - 1 - i)) + psum ρ₀ (m - j) := by
  induction j generalizing m with
  | zero => simp only [Nat.min_zero, range_zero, sum_empty, Nat.sub_zero, zero_add]; rfl
  | succ j ih =>
    rcases m with _ | m
    · simp only [psum_zero, Nat.zero_min, range_zero, sum_empty, Nat.zero_sub, add_zero]
    · show psum (Fin.cons (c j) (consAlt c ρ₀ j) : Fin (n₀ + j + 1) → ℝ) (m + 1) = _
      rw [psum_cons_succ, ih m, Nat.succ_min_succ, sum_range_succ', show m + 1 - (j + 1) = m - j by omega]
      have e : ∀ i ∈ range (min m j), c (j + 1 - 1 - (i + 1)) = c (j - 1 - i) := fun i _ => by
        congr 1; omega
      rw [sum_congr rfl e, show j + 1 - 1 - 0 = j by omega]
      ring

end Psum

/-! ### `IsStageWordN` in prefix-sum form -/

section StageWord

variable {κ : ℝ}

/-- **`IsStageWordN` from prefix sums**: a nonempty left word with total `κ − 4` and proper prefix sums
`≥ κ/2 − 2`, and a right word with prefix sums `≥ κ/2 − 2` and total `κ/2 − 2`. -/
theorem isStageWordN_of_psum {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hn : 0 < nL)
    (hL : psum ρL nL = κ - 4) (hLp : ∀ m, 1 ≤ m → m < nL → κ / 2 - 2 ≤ psum ρL m)
    (hRp : ∀ m, 1 ≤ m → m ≤ nR → κ / 2 - 2 ≤ psum ρR m) (hR : psum ρR nR = κ / 2 - 2) :
    IsStageWordN κ ρL ρR := by
  obtain ⟨m, rfl⟩ : ∃ m, nL = m + 1 := ⟨nL - 1, by omega⟩
  refine ⟨m, rfl, ?_, ⟨fun j => ?_, fun j => ?_⟩, ?_⟩
  · simp only [Fin.cast_eq_self]
    rw [← psum_of_le _ le_rfl]
    exact hL
  · simp only [Fin.cast_eq_self]
    rw [sum_Iic_init_eq_psum]
    exact hLp _ (by omega) (by omega)
  · rw [sum_Iic_eq_psum]
    exact hRp _ (by omega) j.2
  · rw [← psum_of_le _ le_rfl]
    exact hR

/-- The prefix-sum form of `IsStageWordN`. -/
theorem IsStageWordN.psum_cond {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h : IsStageWordN κ ρL ρR) :
    0 < nL ∧ psum ρL nL = κ - 4 ∧ (∀ m, 1 ≤ m → m < nL → κ / 2 - 2 ≤ psum ρL m) ∧
      (∀ m, 1 ≤ m → m ≤ nR → κ / 2 - 2 ≤ psum ρR m) ∧ psum ρR nR = κ / 2 - 2 := by
  obtain ⟨m, rfl, hsL, ⟨hpL, hpR⟩, hsR⟩ := h
  simp only [Fin.cast_eq_self] at hsL hpL
  refine ⟨Nat.succ_pos m, by rw [psum_of_le _ le_rfl]; exact hsL, fun k hk1 hk => ?_, fun k hk1 hk => ?_,
    by rw [psum_of_le _ le_rfl]; exact hsR⟩
  · have h := hpL ⟨k - 1, by omega⟩
    rw [sum_Iic_init_eq_psum] at h
    have e : k - 1 + 1 = k := by omega
    simp only [e] at h
    exact h
  · have h := hpR ⟨k - 1, by omega⟩
    rw [sum_Iic_eq_psum] at h
    have e : k - 1 + 1 = k := by omega
    simp only [e] at h
    exact h

end StageWord

/-! ### The alternating new weights -/

section Alt

variable {κ : ℝ}

/-- The sum of the first `n` new left weights at depth `j` (the most recent first). -/
def newSumL (κ : ℝ) (j n : ℕ) : ℝ := ∑ i ∈ range n, newL κ (j - 1 - i)

theorem sum_range_neg_one_pow (n : ℕ) : ∑ i ∈ range n, (-1 : ℝ) ^ i = if Even n then 0 else 1 := by
  induction n with
  | zero => simp only [range_zero, sum_empty, Even.zero, ↓reduceIte]
  | succ n ih =>
    rw [sum_range_succ, ih]
    by_cases hn : Even n
    · have hn' : ¬ Even (n + 1) := Nat.not_even_iff_odd.2 hn.add_one
      simp only [hn, hn', ↓reduceIte, hn.neg_one_pow, zero_add]
    · have hn' : Even (n + 1) := (Nat.not_even_iff_odd.1 hn).add_one
      simp only [hn, hn', ↓reduceIte, (Nat.not_even_iff_odd.1 hn).neg_one_pow]
      ring

theorem newL_sub (j i : ℕ) (hi : i < j) :
    newL κ (j - 1 - i) = (-1) ^ (j + 1) * (-1) ^ i * angleWeightBound κ := by
  rw [newL, ← pow_add, show j + 1 + i = (j - 1 - i) + 2 * (i + 1) by omega, pow_add, pow_mul]
  norm_num

/-- **The new left partial sums**: `(−1)^{j+1} M` times the parity indicator of `n`. -/
theorem newSumL_eq {j n : ℕ} (hn : n ≤ j) :
    newSumL κ j n = (-1) ^ (j + 1) * angleWeightBound κ * (if Even n then 0 else 1) := by
  rw [newSumL, sum_congr rfl fun i hi => newL_sub j i (lt_of_lt_of_le (mem_range.1 hi) hn),
    ← sum_range_neg_one_pow, mul_sum]
  exact sum_congr rfl fun i _ => by ring

theorem newSumL_bounds_even {j n : ℕ} (hj : Even j) (hn : n ≤ j) (hM : 0 ≤ angleWeightBound κ) :
    -angleWeightBound κ ≤ newSumL κ j n ∧ newSumL κ j n ≤ 0 := by
  rw [newSumL_eq hn, (Nat.not_even_iff_odd.1 (fun h => Nat.not_even_one ((Nat.even_add.1 h).1 hj))).neg_one_pow]
  split_ifs <;> constructor <;> linarith

theorem newSumL_bounds_odd {j n : ℕ} (hj : ¬ Even j) (hn : n ≤ j) (hM : 0 ≤ angleWeightBound κ) :
    0 ≤ newSumL κ j n ∧ newSumL κ j n ≤ angleWeightBound κ := by
  rw [newSumL_eq hn, (Nat.not_even_iff_odd.1 hj).add_one.neg_one_pow]
  split_ifs <;> constructor <;> linarith

theorem newSumL_self_even {j : ℕ} (hj : Even j) : newSumL κ j j = 0 := by
  rw [newSumL_eq le_rfl]; simp only [hj, ↓reduceIte, mul_zero]

theorem newSumL_self_odd {j : ℕ} (hj : ¬ Even j) : newSumL κ j j = angleWeightBound κ := by
  rw [newSumL_eq le_rfl, (Nat.not_even_iff_odd.1 hj).add_one.neg_one_pow]
  simp only [hj, ↓reduceIte, one_mul, mul_one]

/-- The prefix sums of the left stage word. -/
theorem psum_stageρL {nL₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (j m : ℕ) :
    psum (stageρL κ ρL₀ j) m = newSumL κ j (min m j) + psum ρL₀ (m - j) :=
  psum_consAlt (newL κ) ρL₀ j m

/-- The prefix sums of the right stage word (the new right weights are the negatives of the left ones). -/
theorem psum_stageρR {nR₀ : ℕ} (ρR₀ : Fin nR₀ → ℝ) (j m : ℕ) :
    psum (stageρR κ ρR₀ j) m = -newSumL κ j (min m j) + psum ρR₀ (m - j) := by
  rw [stageρR, psum_consAlt, newSumL, ← sum_neg_distrib]
  rfl

end Alt

/-! ### The initial word -/

section Init

variable {κ : ℝ}

/-- **The conditions on the initial word** of the alternating construction: left total `κ − 4`, right total
`κ/2 − 2`, left proper prefix sums `≥ κ/2 − 2`, right proper prefix sums `≥ 0`. -/
def IsStageInit (κ : ℝ) {nL₀ nR₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) : Prop :=
  psum ρL₀ nL₀ = κ - 4 ∧ psum ρR₀ nR₀ = κ / 2 - 2 ∧ (∀ m, 1 ≤ m → m < nL₀ → κ / 2 - 2 ≤ psum ρL₀ m) ∧
    ∀ m, 1 ≤ m → m < nR₀ → 0 ≤ psum ρR₀ m

variable {nL₀ nR₀ : ℕ} {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}

theorem IsStageInit.pos_left (hκ4 : κ < 4) (h : IsStageInit κ ρL₀ ρR₀) : 0 < nL₀ := by
  rcases Nat.eq_zero_or_pos nL₀ with h0 | h0
  · subst h0
    have := h.1
    rw [psum_zero] at this
    linarith
  · exact h0

/-- **The leftward stages** (`hwL` of `ae_not_isBounded_of_stageLaw`): at every even depth the stage word is a stage
word. -/
theorem hwL_of_isStageInit (hκ : 0 < κ) (hκ4 : κ < 4) (h : IsStageInit κ ρL₀ ρR₀) :
    ∀ j, Even j → IsStageWordN κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j) := by
  intro j hj
  obtain ⟨hL, hR, hLp, hRp⟩ := h
  have hM := angleWeightBound_eq hκ
  have hM0 : 0 ≤ angleWeightBound κ := (angleWeightBound_pos hκ hκ4).le
  have hn := IsStageInit.pos_left hκ4 ⟨hL, hR, hLp, hRp⟩
  refine isStageWordN_of_psum (by omega) ?_ (fun m hm1 hm => ?_) (fun m hm1 hm => ?_) ?_
  · rw [psum_stageρL, min_eq_right (by omega), Nat.add_sub_cancel, newSumL_self_even hj, hL, zero_add]
  · rw [psum_stageρL]
    by_cases hmj : m ≤ j
    · rw [min_eq_left hmj, Nat.sub_eq_zero_of_le hmj, psum_zero, add_zero]
      linarith [(newSumL_bounds_even hj hmj hM0).1]
    · rw [min_eq_right (by omega), newSumL_self_even hj, zero_add]
      exact hLp _ (by omega) (by omega)
  · rw [psum_stageρR]
    by_cases hmj : m ≤ j
    · rw [min_eq_left hmj, Nat.sub_eq_zero_of_le hmj, psum_zero, add_zero]
      linarith [(newSumL_bounds_even hj hmj hM0).2]
    · rw [min_eq_right (by omega), newSumL_self_even hj, neg_zero, zero_add]
      by_cases hmn : m - j < nR₀
      · linarith [hRp (m - j) (by omega) hmn]
      · rw [show m - j = nR₀ by omega, hR]
  · rw [psum_stageρR, min_eq_right (by omega), Nat.add_sub_cancel, newSumL_self_even hj, neg_zero, hR, zero_add]

/-- **The rightward stages** (`hwR` of `ae_not_isBounded_of_stageLaw`): at every odd depth the reflected stage word is a
stage word. -/
theorem hwR_of_isStageInit (hκ : 0 < κ) (hκ4 : κ < 4) (h : IsStageInit κ ρL₀ ρR₀) :
    ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ ρR₀ j) (stageρL κ ρL₀ j) := by
  intro j hj
  obtain ⟨hL, hR, hLp, hRp⟩ := h
  have hM := angleWeightBound_eq hκ
  have hM0 : 0 ≤ angleWeightBound κ := (angleWeightBound_pos hκ hκ4).le
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exact absurd (h0 ▸ Even.zero) hj
    · exact h0
  refine isStageWordN_of_psum (by omega) ?_ (fun m hm1 hm => ?_) (fun m hm1 hm => ?_) ?_
  · rw [psum_stageρR, min_eq_right (by omega), Nat.add_sub_cancel, newSumL_self_odd hj, hR, hM]
    ring
  · rw [psum_stageρR]
    by_cases hmj : m ≤ j
    · rw [min_eq_left hmj, Nat.sub_eq_zero_of_le hmj, psum_zero, add_zero]
      linarith [(newSumL_bounds_odd hj hmj hM0).2]
    · rw [min_eq_right (by omega), newSumL_self_odd hj]
      linarith [hRp (m - j) (by omega) (by omega)]
  · rw [psum_stageρL]
    by_cases hmj : m ≤ j
    · rw [min_eq_left hmj, Nat.sub_eq_zero_of_le hmj, psum_zero, add_zero]
      linarith [(newSumL_bounds_odd hj hmj hM0).1]
    · rw [min_eq_right (by omega), newSumL_self_odd hj]
      by_cases hmn : m - j < nL₀
      · linarith [hLp (m - j) (by omega) hmn]
      · rw [show m - j = nL₀ by omega, hL]
        linarith
  · rw [psum_stageρL, min_eq_right (by omega), Nat.add_sub_cancel, newSumL_self_odd hj, hL, hM]
    ring

/-- **The converse**: the stage-word conditions at depths `0` and `1` imply `IsStageInit`; so `IsStageInit` is
exactly the content of `hwL` and `hwR`. -/
theorem isStageInit_of_hw (hκ : 0 < κ)
    (hwL : ∀ j, Even j → IsStageWordN κ (stageρL κ ρL₀ j) (stageρR κ ρR₀ j))
    (hwR : ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ ρR₀ j) (stageρL κ ρL₀ j)) : IsStageInit κ ρL₀ ρR₀ := by
  obtain ⟨-, hL, hLp, -, hR⟩ := (hwL 0 Even.zero).psum_cond
  obtain ⟨-, -, hRp1, -, -⟩ := (hwR 1 Nat.not_even_one).psum_cond
  refine ⟨hL, hR, hLp, fun m hm1 hm => ?_⟩
  have h := hRp1 (m + 1) (by omega) (by omega)
  have e : psum (stageρR κ ρR₀ 1) (m + 1) = newR κ 0 + psum ρR₀ m := psum_cons_succ _ _ _
  rw [e, newR, pow_zero, one_mul, angleWeightBound_eq hκ] at h
  linarith

end Init

end Prop59Stage

end Sec5

end InteractingSLE
