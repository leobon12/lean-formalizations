/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalWord
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalFlow

/-!
# The staged cross-conditioning law: the levels of the iterated stop word are the born marks

Packet PROVE-CROSSCOND-STAGED4 (S2). The levels `levL k u`, `levR k u` of the iterated stop word
(`CrossCondStagedFinalWord`) are iterated record positions. If the record drivers are the pieces of one concatenated
driver `V` (piece `i` is `shiftDrive V (S i)` on `[0, T i]`, `S i = T 0 + ⋯ + T (i − 1)` its start) and the base images
of the shifted chains stay off the driver (the gap hypotheses, which hold for a simple trace), then

* **`levLs_eq_chartAL`**: `levL k u j = chartAL (shiftDrive V (S j)) (S k − S j)` for `j ≤ k`;
* **`levRs_eq_chartAR`**: `levR k u j = chartAR (shiftDrive V (S j)) (S k − S j)`,

i.e. the levels are the base images of the chain shifted at the switch times — the born marks of PROVE-CROSSCOND-STAGED3
(`IsBornPairL/R`), with the outer base `chartAL V (S k)` at `j = 0` and the tip `0` at `j = k`. The induction step
is the flow property of the base images (`markPosL_shiftDrive_chartAL`, `markPos_shiftDrive_chartAR`) and, at a new
switch, the seed identity (`markPosL_zero_eq_chartAL`, `markPos_zero_eq_chartAR`).

Deterministic; R48: no Theorem 1.2/1.3 input.
-/

set_option autoImplicit false

noncomputable section

open Set
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Sec5.CrossCond.StagedFinal

open Exist.StagedLaw Exist.Staged Restart Sec7.StripSideHeightProb MartChar.RealFlow
open WangWu (chartAL chartAR)

/-! ### Start times and shifted drivers -/

section Start

/-- The start time of piece `j`: `T 0 + ⋯ + T (j − 1)`. -/
def startT (T : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.range j, T i

theorem startT_zero (T : ℕ → ℝ) : startT T 0 = 0 := by simp [startT]

theorem startT_succ (T : ℕ → ℝ) (j : ℕ) : startT T (j + 1) = startT T j + T j := by
  simp only [startT, Finset.sum_range_succ]

theorem startT_mono {T : ℕ → ℝ} (hT : ∀ i, 0 ≤ T i) {i j : ℕ} (hij : i ≤ j) : startT T i ≤ startT T j := by
  induction j with
  | zero => obtain rfl := Nat.le_zero.1 hij; exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · rw [startT_succ]
      have := ih (Nat.lt_succ_iff.1 h)
      linarith [hT j]
    · obtain rfl : i = j + 1 := le_antisymm hij h
      exact le_rfl

theorem shiftDrive_shiftDrive (V : ℝ → ℝ) (a b : ℝ) : shiftDrive (shiftDrive V a) b = shiftDrive V (a + b) := by
  funext r
  simp only [shiftDrive, add_assoc]
  ring

theorem shiftDrive_zero_apply (V : ℝ → ℝ) (a : ℝ) : shiftDrive V a 0 = 0 := by
  simp only [shiftDrive, add_zero, sub_self]

theorem chartAL_zero {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) : chartAL W 0 = 0 := by
  unfold chartAL
  rw [rightImg_zero (w := fun s => -W s) hW.neg (by simp [hW0]) le_rfl, hW0]
  ring

theorem chartAR_zero {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) : chartAR W 0 = 0 := by
  unfold chartAR
  rw [rightImg_zero hW hW0 le_rfl, hW0, sub_zero]

end Start

/-! ### The levels of sequences of records -/

section Seq

/-- The left levels for a sequence of drivers and times. -/
def levLs (w : ℕ → ℝ → ℝ) (T : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | k + 1 => nextLev (markPosL (w k) (T k)) k (levLs w T k)

/-- The right levels for a sequence of drivers and times. -/
def levRs (w : ℕ → ℝ → ℝ) (T : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | k + 1 => nextLev (markPos (w k) (T k)) k (levRs w T k)

theorem levLs_congr {w w' : ℕ → ℝ → ℝ} {T T' : ℕ → ℝ} :
    ∀ k, (∀ i < k, w i = w' i ∧ T i = T' i) → levLs w T k = levLs w' T' k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := levLs_congr k fun i hi => h i (Nat.lt_succ_of_lt hi)
    obtain ⟨h1, h2⟩ := h k (Nat.lt_succ_self k)
    simp only [levLs, ih, h1, h2]

theorem levRs_congr {w w' : ℕ → ℝ → ℝ} {T T' : ℕ → ℝ} :
    ∀ k, (∀ i < k, w i = w' i ∧ T i = T' i) → levRs w T k = levRs w' T' k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := levRs_congr k fun i hi => h i (Nat.lt_succ_of_lt hi)
    obtain ⟨h1, h2⟩ := h k (Nat.lt_succ_self k)
    simp only [levRs, ih, h1, h2]

/-- The record drivers of a retained past, as a sequence (`0` after the last record). -/
def recSeqW {k : ℕ} (u : PastData k) (i : ℕ) : ℝ → ℝ := if h : i < k then rdrv (u ⟨i, h⟩) else fun _ => 0

/-- The record times of a retained past, as a sequence (`0` after the last record). -/
def recSeqT {k : ℕ} (u : PastData k) (i : ℕ) : ℝ := if h : i < k then rtime (u ⟨i, h⟩) else 0

theorem levL_eq_levLs : ∀ (k : ℕ) (u : PastData k), levL k u = levLs (recSeqW u) (recSeqT u) k
  | 0, _ => rfl
  | k + 1, u => by
    have ih := levL_eq_levLs k (Fin.init (α := fun _ => RecData) u)
    have hc := levLs_congr (w := recSeqW (Fin.init (α := fun _ => RecData) u)) (w' := recSeqW u)
      (T := recSeqT (Fin.init (α := fun _ => RecData) u)) (T' := recSeqT u) k fun i hi => by
        simp only [recSeqW, recSeqT, hi, Nat.lt_succ_of_lt hi, ↓reduceDIte]
        exact ⟨rfl, rfl⟩
    have hk : recSeqW u k = rdrv (u (Fin.last k)) ∧ recSeqT u k = rtime (u (Fin.last k)) := by
      simp only [recSeqW, recSeqT, Nat.lt_succ_self k, ↓reduceDIte]
      exact ⟨rfl, rfl⟩
    change nextLev (markPosL (rdrv (u (Fin.last k))) (rtime (u (Fin.last k)))) k
      (levL k (Fin.init (α := fun _ => RecData) u)) = nextLev (markPosL (recSeqW u k) (recSeqT u k)) k
        (levLs (recSeqW u) (recSeqT u) k)
    rw [ih, hc, hk.1, hk.2]

theorem levR_eq_levRs : ∀ (k : ℕ) (u : PastData k), levR k u = levRs (recSeqW u) (recSeqT u) k
  | 0, _ => rfl
  | k + 1, u => by
    have ih := levR_eq_levRs k (Fin.init (α := fun _ => RecData) u)
    have hc := levRs_congr (w := recSeqW (Fin.init (α := fun _ => RecData) u)) (w' := recSeqW u)
      (T := recSeqT (Fin.init (α := fun _ => RecData) u)) (T' := recSeqT u) k fun i hi => by
        simp only [recSeqW, recSeqT, hi, Nat.lt_succ_of_lt hi, ↓reduceDIte]
        exact ⟨rfl, rfl⟩
    have hk : recSeqW u k = rdrv (u (Fin.last k)) ∧ recSeqT u k = rtime (u (Fin.last k)) := by
      simp only [recSeqW, recSeqT, Nat.lt_succ_self k, ↓reduceDIte]
      exact ⟨rfl, rfl⟩
    change nextLev (markPos (rdrv (u (Fin.last k))) (rtime (u (Fin.last k)))) k
      (levR k (Fin.init (α := fun _ => RecData) u)) = nextLev (markPos (recSeqW u k) (recSeqT u k)) k
        (levRs (recSeqW u) (recSeqT u) k)
    rw [ih, hc, hk.1, hk.2]

end Seq

/-! ### The levels are the base images of the shifted chains -/

section Base

variable {w : ℕ → ℝ → ℝ} {T : ℕ → ℝ} {V : ℝ → ℝ}

/-- **The left levels are the left base images of the shifted chains.** If piece `i` is `shiftDrive V (S i)` on
`[0, T i]` and the left base images of the shifted chains stay strictly left of the driver up to the time `S K`, then
for `k ≤ K`, `j ≤ k`: `levLs w T k j = chartAL (shiftDrive V (S j)) (S k − S j)`. -/
theorem levLs_eq_chartAL (hV : Continuous V) (hT : ∀ i, 0 ≤ T i)
    (hw : ∀ i, EqOn (w i) (shiftDrive V (startT T i)) (Icc 0 (T i))) {K : ℕ}
    (hgap : ∀ j < K, ∀ r, 0 < r → r ≤ startT T K - startT T j → chartAL (shiftDrive V (startT T j)) r < 0) :
    ∀ k ≤ K, ∀ j ≤ k, levLs w T k j = chartAL (shiftDrive V (startT T j)) (startT T k - startT T j) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    obtain rfl := Nat.le_zero.1 hj
    rw [sub_self, chartAL_zero (QuantumZipper.RS.continuous_shiftDrive hV _) (shiftDrive_zero_apply _ _)]
    rfl
  | succ k ih =>
    intro hk j hj
    have hVs : ∀ a, Continuous (shiftDrive V a) := fun a => QuantumZipper.RS.continuous_shiftDrive hV a
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · have hjk' := Nat.lt_succ_iff.1 hjk
      change nextLev (markPosL (w k) (T k)) k (levLs w T k) j = _
      rw [nextLev_of_le hjk', ih (Nat.le_of_succ_le hk) j hjk', markPosL_congr (hw k)]
      set s := startT T k - startT T j with hs
      have hs0 : 0 ≤ s := sub_nonneg.2 (startT_mono hT hjk')
      have hsk : startT T k = startT T j + s := by rw [hs]; ring
      have hk1 : startT T (k + 1) - startT T j = s + T k := by rw [startT_succ, hsk]; ring
      rw [hk1, hsk, ← shiftDrive_shiftDrive]
      rcases hs0.lt_or_eq with hpos | hzero
      · refine markPosL_shiftDrive_chartAL (hVs _) hpos (hT k) fun r hr => ?_
        refine hgap j (lt_of_le_of_lt hjk' (Nat.lt_of_succ_le hk)) r (hpos.trans_le hr.1) ?_
        have hK := startT_mono hT hk
        rw [startT_succ] at hK
        linarith [hr.2]
      · rw [← hzero, zero_add, chartAL_zero (hVs _) (shiftDrive_zero_apply _ _)]
        rw [show shiftDrive (shiftDrive V (startT T j)) 0 = shiftDrive V (startT T j) by
          rw [shiftDrive_shiftDrive, add_zero]]
        exact markPosL_zero_eq_chartAL (hVs _) (shiftDrive_zero_apply _ _) (hT k)
    · obtain rfl : j = k + 1 := le_antisymm hj hjk
      change nextLev (markPosL (w k) (T k)) k (levLs w T k) (k + 1) = _
      rw [nextLev_succ, sub_self, chartAL_zero (hVs _) (shiftDrive_zero_apply _ _)]

/-- **The right levels are the right base images of the shifted chains** (mirror of `levLs_eq_chartAL`). -/
theorem levRs_eq_chartAR (hV : Continuous V) (hT : ∀ i, 0 ≤ T i)
    (hw : ∀ i, EqOn (w i) (shiftDrive V (startT T i)) (Icc 0 (T i))) {K : ℕ}
    (hgap : ∀ j < K, ∀ r, 0 < r → r ≤ startT T K - startT T j → 0 < chartAR (shiftDrive V (startT T j)) r) :
    ∀ k ≤ K, ∀ j ≤ k, levRs w T k j = chartAR (shiftDrive V (startT T j)) (startT T k - startT T j) := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    obtain rfl := Nat.le_zero.1 hj
    rw [sub_self, chartAR_zero (QuantumZipper.RS.continuous_shiftDrive hV _) (shiftDrive_zero_apply _ _)]
    rfl
  | succ k ih =>
    intro hk j hj
    have hVs : ∀ a, Continuous (shiftDrive V a) := fun a => QuantumZipper.RS.continuous_shiftDrive hV a
    rcases Nat.lt_or_ge j (k + 1) with hjk | hjk
    · have hjk' := Nat.lt_succ_iff.1 hjk
      change nextLev (markPos (w k) (T k)) k (levRs w T k) j = _
      rw [nextLev_of_le hjk', ih (Nat.le_of_succ_le hk) j hjk', markPos_congr (hw k)]
      set s := startT T k - startT T j with hs
      have hs0 : 0 ≤ s := sub_nonneg.2 (startT_mono hT hjk')
      have hsk : startT T k = startT T j + s := by rw [hs]; ring
      have hk1 : startT T (k + 1) - startT T j = s + T k := by rw [startT_succ, hsk]; ring
      rw [hk1, hsk, ← shiftDrive_shiftDrive]
      rcases hs0.lt_or_eq with hpos | hzero
      · refine markPos_shiftDrive_chartAR (hVs _) hpos (hT k) fun r hr => ?_
        refine hgap j (lt_of_le_of_lt hjk' (Nat.lt_of_succ_le hk)) r (hpos.trans_le hr.1) ?_
        have hK := startT_mono hT hk
        rw [startT_succ] at hK
        linarith [hr.2]
      · rw [← hzero, zero_add, chartAR_zero (hVs _) (shiftDrive_zero_apply _ _)]
        rw [show shiftDrive (shiftDrive V (startT T j)) 0 = shiftDrive V (startT T j) by
          rw [shiftDrive_shiftDrive, add_zero]]
        exact markPos_zero_eq_chartAR (hVs _) (shiftDrive_zero_apply _ _) (hT k)
    · obtain rfl : j = k + 1 := le_antisymm hj hjk
      change nextLev (markPos (w k) (T k)) k (levRs w T k) (k + 1) = _
      rw [nextLev_succ, sub_self, chartAR_zero (hVs _) (shiftDrive_zero_apply _ _)]

end Base

end InteractingSLE.Sec5.CrossCond.StagedFinal
