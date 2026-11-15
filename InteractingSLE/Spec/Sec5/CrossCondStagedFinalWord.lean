/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSideHeightProbSide
import InteractingSLE.Spec.Restart.RetAux79Zone
import InteractingSLE.Spec.Supplement.GW2SchedulePast

/-!
# The staged cross-conditioning law: the side heights of an iterated stop word

Packet PROVE-CROSSCOND-STAGED4 (S2). The word of the field after the stopped pieces `0, …, k − 1` of a flow program
is the iterated stop word `pastWord (stopWord κ) c₀ x₀ θ k u` of the records `u` (`Theorem14.GW2Schedule.pastWord`,
the explicit witness of `GW2Schedule.stageWitness_all`). Read in the chart after the pieces, its data on the real
line are the side heights of the pieces: the left side of piece `j` occupies an interval `(p j, p (j + 1))` and carries
`−λ − θ_j χ`, the right side an interval `(q (j + 1), q j)` with `λ − θ_j χ`; the levels `p j`, `q j` are the record
positions of the switch point of piece `j` (`p k = q k = 0` is the tip). The jumps of the word between `p 0` and `q 0`
are exactly the intermediate levels (the marks born at the switches).

* `IsLeftLevels c k p ht`, `IsRightLevels c k q ht`: these properties of a word `c` after `k` pieces;
* **`isLeftLevels_stopWord`**, **`isRightLevels_stopWord`**: one more piece (the stop word of a record) moves every
  level by the record position of the piece (`nextLev`) and adds the new piece's sides `∓λ − θχ` next to the tip;
* **`isLeftLevels_pastWord`**, **`isRightLevels_pastWord`**: hence the iterated stop word of any records, with the
  levels `levL`, `levR` (iterated record positions) and the heights `∓λ − θ_j χ`.

The step uses only that record positions are monotone and signed (`markPosL_anti`, `markPos_mono`), the structure of
the stop word's marks (the record positions of the seed and of the old jumps), and the flow-line data identity
`Exist.forceBoundaryData_flowLine_seed`. Deterministic; R48: no Theorem 1.2/1.3 input.
-/

set_option autoImplicit false

noncomputable section

open Set
open QuantumZipper (chiC)

namespace InteractingSLE.Sec5.CrossCond.StagedFinal

open Exist.StagedLaw Exist.Staged Restart Sec7.StripSideHeightProb

/-! ### Monotone level sequences -/

section Mono

theorem le_of_succ_le' {p : ℕ → ℝ} {k : ℕ} (hp : ∀ j < k, p j ≤ p (j + 1)) :
    ∀ i j, i ≤ j → j ≤ k → p i ≤ p j := by
  intro i j hij hjk
  induction j with
  | zero => obtain rfl := Nat.le_zero.1 hij; exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.1 h) (by omega)).trans (hp j (by omega))
    · obtain rfl : i = j + 1 := le_antisymm hij h
      exact le_rfl

theorem ge_of_succ_ge' {q : ℕ → ℝ} {k : ℕ} (hq : ∀ j < k, q (j + 1) ≤ q j) :
    ∀ i j, i ≤ j → j ≤ k → q j ≤ q i := by
  have h := le_of_succ_le' (p := fun j => -q j) (k := k) fun j hj => neg_le_neg (hq j hj)
  intro i j hij hjk
  have := h i j hij hjk
  linarith

end Mono

/-! ### The marks and the data of a stop word -/

section StopWord

variable {κ : ℝ}

/-- **The jumps of a stop word**: the record positions of the left marks of the flow-line word, the tip `0`, and the
record positions of its right marks. -/
theorem mem_jumps_stopWord {c : BoundaryWord} {θ : ℝ} {r : RecData} {y : ℝ}
    (hy : y ∈ (stopWord κ (c, θ, r)).jumps) :
    (∃ i : Fin (flowLineNL c.fn c.jumps 0), y = markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i)) ∨
      y = 0 ∨ ∃ j : Fin (flowLineNR c.fn c.jumps 0), y = markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j) := by
  obtain ⟨m, hm, hmy⟩ := BoundaryWord.mem_jumps.1 hy
  have hord := isMarkOrder_stopWord c r
  change m < flowLineNL c.fn c.jumps 0 + 1 + flowLineNR c.fn c.jumps 0 at hm
  change cumMax (rawPos (flowLineNL c.fn c.jumps 0)
    (fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
    (fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))) m = y at hmy
  rw [cumMax_rawPos hord hm] at hmy
  unfold rawPos at hmy
  split_ifs at hmy with h1 h2
  · left
    refine ⟨⟨flowLineNL c.fn c.jumps 0 - 1 - m, by omega⟩, ?_⟩
    rw [← hmy]
    simp only [padFL, show flowLineNL c.fn c.jumps 0 - 1 - m < flowLineNL c.fn c.jumps 0 by omega, ↓reduceDIte]
  · exact Or.inr (Or.inl hmy.symm)
  · right; right
    refine ⟨⟨m - flowLineNL c.fn c.jumps 0 - 1, by omega⟩, ?_⟩
    rw [← hmy]
    simp only [padFL, show m - flowLineNL c.fn c.jumps 0 - 1 < flowLineNR c.fn c.jumps 0 by omega, ↓reduceDIte]

/-- **The data of a stop word** off its jumps and the tip: the force data of the flow-line word at the record positions,
minus `θχ`. -/
theorem fn_stopWord (c : BoundaryWord) (θ : ℝ) (r : RecData) {y : ℝ} (hy : y ∉ (stopWord κ (c, θ, r)).jumps)
    (hy0 : y ≠ 0) :
    (stopWord κ (c, θ, r)).fn y =
      forceBoundaryData κ (fun i : Fin (flowLineNL c.fn c.jumps 0) => flowLineRhoL κ c.fn c.jumps 0 θ i)
        (fun j : Fin (flowLineNR c.fn c.jumps 0) => flowLineRhoR κ c.fn c.jumps 0 θ j)
        (fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i))
        (fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j)) y - θ * chiC κ := by
  have h := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ)
    (isMarkOrder_stopWord c r) hy hy0
  have e1 : (fun i : Fin (flowLineNL c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.1 i) =
      fun i => flowLineRhoL κ c.fn c.jumps 0 θ i := funext fun i => by simp only [padFL, i.2, ↓reduceDIte, Fin.eta]
  have e2 : (fun j : Fin (flowLineNR c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.2 j) =
      fun j => flowLineRhoR κ c.fn c.jumps 0 θ j := funext fun j => by simp only [padFL, j.2, ↓reduceDIte, Fin.eta]
  have e3 : (fun i : Fin (flowLineNL c.fn c.jumps 0) =>
      markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i)) =
      fun i => markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i) :=
    funext fun i => by simp only [padFL, i.2, ↓reduceDIte, Fin.eta]
  have e4 : (fun j : Fin (flowLineNR c.fn c.jumps 0) =>
      markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) =
      fun j => markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j) :=
    funext fun j => by simp only [padFL, j.2, ↓reduceDIte, Fin.eta]
  rw [e1, e2, e3, e4] at h
  exact h

end StopWord

/-! ### Left levels -/

section Left

variable {κ : ℝ}

/-- **The left levels of a word after `k` pieces**: `p k = 0` (the tip), the levels increase, the jumps of the word in
`(p 0, 0)` are intermediate levels `p j` (`1 ≤ j < k`), and on the open interval `(p j, p (j + 1))` the data are
`ht j`. -/
def IsLeftLevels (c : BoundaryWord) (k : ℕ) (p ht : ℕ → ℝ) : Prop :=
  p k = 0 ∧ (∀ j < k, p j ≤ p (j + 1)) ∧
    (∀ y ∈ c.jumps, p 0 < y → y < 0 → ∃ j, 1 ≤ j ∧ j < k ∧ y = p j) ∧
    ∀ j < k, ∀ y, p j < y → y < p (j + 1) → y ∉ c.jumps → c.fn y = ht j

/-- The levels after one more piece: each old level moved by the record position `L`, and the new tip `0`. -/
def nextLev (L : ℝ → ℝ) (k : ℕ) (p : ℕ → ℝ) (j : ℕ) : ℝ := if j ≤ k then L (p j) else 0

theorem nextLev_of_le {L : ℝ → ℝ} {k : ℕ} {p : ℕ → ℝ} {j : ℕ} (hj : j ≤ k) : nextLev L k p j = L (p j) := by
  simp only [nextLev, hj, ↓reduceIte]

theorem nextLev_succ (L : ℝ → ℝ) (k : ℕ) (p : ℕ → ℝ) : nextLev L k p (k + 1) = 0 := by
  simp only [nextLev, show ¬ k + 1 ≤ k by omega, ↓reduceIte]

theorem IsLeftLevels.congr_ht {c : BoundaryWord} {k : ℕ} {p ht ht' : ℕ → ℝ} (h : IsLeftLevels c k p ht)
    (he : ∀ j < k, ht j = ht' j) : IsLeftLevels c k p ht' :=
  ⟨h.1, h.2.1, h.2.2.1, fun j hj y h1 h2 h3 => (h.2.2.2 j hj y h1 h2 h3).trans (he j hj)⟩

/-- Before any piece: the single level `0`. -/
theorem isLeftLevels_zero (c : BoundaryWord) (ht : ℕ → ℝ) : IsLeftLevels c 0 (fun _ => 0) ht :=
  ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j), fun _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl 0),
    fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- **One more piece, left side.** If `c` has the left levels `p` with heights `ht` after `k` pieces, the stop word of
a record `r` at angle `θ` has the left levels `nextLev L k p` (`L` the record position of left marks) after `k + 1`
pieces, with the heights `ht` and the new piece's left side `−λ − θχ`. -/
theorem isLeftLevels_stopWord (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {k : ℕ} {p ht : ℕ → ℝ}
    (h : IsLeftLevels c k p ht) :
    IsLeftLevels (stopWord κ (c, θ, r)) (k + 1) (nextLev (markPosL (rdrv r) (rtime r)) k p)
      (fun j => if j < k then ht j else -sleLambda κ - θ * chiC κ) := by
  classical
  obtain ⟨hpk, hpm, hpJ, hpf⟩ := h
  set L := markPosL (rdrv r) (rtime r) with hLdef
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hLm : ∀ {x' x : ℝ}, x' ≤ x → x ≤ 0 → L x' ≤ L x := fun hx'x hx => markPosL_anti hw hw0 hT hx hx'x
  have hLn : ∀ {x : ℝ}, x ≤ 0 → L x ≤ 0 := fun hx => markPosL_nonpos hw hw0 hT hx
  have hmono := le_of_succ_le' hpm
  have hp0 : ∀ j ≤ k, p j ≤ 0 := fun j hj => hpk ▸ hmono j k hj le_rfl
  set xL := flowLineXL c.fn c.jumps 0 with hxLdef
  have hxL : ∀ i, xL i = 0 ∨ (xL i < 0 ∧ xL i ∈ c.jumps) := Restart.RetAux79.flowLineXL_eq_zero_or_mem c
  have hxLn : ∀ i, xL i ≤ 0 := fun i => by
    rcases hxL i with h0 | ⟨h0, -⟩
    · exact h0.le
    · exact h0.le
  have hxR := Restart.RetAux79.flowLineXR_eq_zero_or_mem c
  -- the structure of the old marks right of `p 0`
  have hmark : ∀ i, p 0 < xL i → xL i = 0 ∨ ∃ m, 1 ≤ m ∧ m < k ∧ xL i = p m := by
    intro i hi
    rcases hxL i with h0 | ⟨h0, hJ⟩
    · exact Or.inl h0
    · exact Or.inr (hpJ _ hJ hi h0)
  refine ⟨nextLev_succ _ _ _, fun j hj => ?_, fun y hy h1 h2 => ?_, fun j hj x h1 h2 hxJ => ?_⟩
  · -- the new levels increase
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [nextLev_of_le hjk.le, nextLev_of_le hjk]
      exact hLm (hpm j hjk) (hp0 _ hjk)
    · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) hjk
      rw [nextLev_of_le le_rfl, nextLev_succ]
      exact hLn (hp0 _ le_rfl)
  · -- the jumps of the new word between the outer level and the tip
    rw [nextLev_of_le (Nat.zero_le k)] at h1
    rcases mem_jumps_stopWord hy with ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩
    · have hpi : p 0 < xL i := by
        by_contra hle
        exact absurd (hLm (not_lt.1 hle) (hp0 0 (Nat.zero_le k))) (not_le.2 h1)
      rcases hmark i hpi with h0 | ⟨m, hm1, hmk, hm⟩
      · have hk0 : k ≠ 0 := by
          rintro rfl
          rw [hpk] at hpi
          linarith [hxLn i]
        refine ⟨k, Nat.one_le_iff_ne_zero.2 hk0, Nat.lt_succ_self k, ?_⟩
        rw [nextLev_of_le le_rfl, hpk]
        show L (xL i) = L 0
        rw [h0]
      · refine ⟨m, hm1, Nat.lt_succ_of_lt hmk, ?_⟩
        rw [nextLev_of_le hmk.le]
        show L (xL i) = L (p m)
        rw [hm]
    · exact absurd h2 (lt_irrefl 0)
    · have : 0 ≤ markPos (rdrv r) (rtime r) (flowLineXR c.fn c.jumps 0 j) := by
        refine markPos_nonneg hw hw0 hT ?_
        rcases hxR j with h0 | ⟨h0, -⟩
        · exact h0.ge
        · exact h0.le
      linarith
  · -- the data on the new intervals
    have hx0 : x < 0 := by
      refine h2.trans_le ?_
      rcases Nat.lt_or_ge (j + 1) (k + 1) with hj1 | hj1
      · rw [nextLev_of_le (Nat.lt_succ_iff.1 hj1)]
        exact hLn (hp0 _ (Nat.lt_succ_iff.1 hj1))
      · rw [show j + 1 = k + 1 by omega, nextLev_succ]
    rw [fn_stopWord c θ r hxJ hx0.ne]
    unfold forceBoundaryData
    simp only [hx0, ↓reduceIte]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · -- an old piece: compare with the old data at a point of the old interval
      rw [nextLev_of_le hjk.le] at h1
      rw [nextLev_of_le hjk] at h2
      have hlt : p j < p (j + 1) := by
        rcases (hpm j hjk).lt_or_eq with h | h
        · exact h
        · rw [h] at h1; exact absurd (h1.trans h2) (lt_irrefl _)
      set y := (p j + p (j + 1)) / 2 with hy
      have hy1 : p j < y := by rw [hy]; linarith
      have hy2 : y < p (j + 1) := by rw [hy]; linarith
      have hy0 : y < 0 := hy2.trans_le (hp0 _ hjk)
      have hpy : p 0 < y := (hmono 0 j (Nat.zero_le j) hjk.le).trans_lt hy1
      have hyJ : y ∉ c.jumps := by
        intro hyJ
        obtain ⟨m, -, hmk, hm⟩ := hpJ y hyJ hpy hy0
        rcases Nat.lt_or_ge m (j + 1) with hmj | hmj
        · have := hmono m j (Nat.lt_succ_iff.1 hmj) hjk.le
          rw [← hm] at this; linarith
        · have := hmono (j + 1) m hmj hmk.le
          rw [← hm] at this; linarith
      have hfilt : (Finset.univ.filter fun i : Fin (flowLineNL c.fn c.jumps 0) => x < L (xL i)) =
          Finset.univ.filter fun i => y < xL i := by
        refine Finset.filter_congr fun i _ => ⟨fun hxi => ?_, fun hyi => ?_⟩
        · by_contra hle
          push Not at hle
          have hle' : xL i ≤ p j := by
            rcases hxL i with h0 | ⟨h0, hJ⟩
            · rw [h0] at hle; linarith
            · by_cases hp : xL i ≤ p 0
              · exact hp.trans (hmono 0 j (Nat.zero_le j) hjk.le)
              · obtain ⟨m, -, hmk, hm⟩ := hpJ _ hJ (not_le.1 hp) h0
                rw [hm] at hle ⊢
                rcases Nat.lt_or_ge m (j + 1) with hmj | hmj
                · exact hmono m j (Nat.lt_succ_iff.1 hmj) hjk.le
                · have := hmono (j + 1) m hmj hmk.le; linarith
          have := hLm hle' (hp0 _ hjk.le)
          linarith
        · have hge : p (j + 1) ≤ xL i := by
            rcases hmark i (hpy.trans hyi) with h0 | ⟨m, -, hmk, hm⟩
            · rw [h0, ← hpk]; exact hmono _ _ hjk le_rfl
            · rw [hm] at hyi ⊢
              rcases Nat.lt_or_ge m (j + 1) with hmj | hmj
              · have := hmono m j (Nat.lt_succ_iff.1 hmj) hjk.le; linarith
              · exact hmono (j + 1) m hmj hmk.le
          exact h2.trans_le (hLm hge (hxLn i))
      rw [hfilt]
      have hseed := Exist.forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 θ hy0.ne
        (by rw [add_zero]; exact hyJ)
      unfold forceBoundaryData at hseed
      simp only [hy0, ↓reduceIte] at hseed
      rw [add_zero, hpf j hjk y hy1 hy2 hyJ] at hseed
      simp only [hjk, ↓reduceIte]
      linarith
    · -- the new piece: no mark right of `x`
      obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) hjk
      rw [nextLev_of_le le_rfl, hpk] at h1
      have hempty : (Finset.univ.filter fun i : Fin (flowLineNL c.fn c.jumps 0) => x < L (xL i)) = ∅ := by
        refine Finset.filter_false_of_mem fun i _ => not_lt.2 ?_
        exact (hLm (hxLn i) le_rfl).trans h1.le
      rw [hempty, Finset.sum_empty, add_zero, mul_one]
      simp only [lt_irrefl, ↓reduceIte, sleLambda]

end Left
/-! ### Right levels -/

section Right

variable {κ : ℝ}

/-- **The right levels of a word after `k` pieces** (mirror of `IsLeftLevels`): `q k = 0`, the levels decrease, the
jumps in `(0, q 0)` are intermediate levels, and on `(q (j + 1), q j)` the data are `ht j`. -/
def IsRightLevels (c : BoundaryWord) (k : ℕ) (q ht : ℕ → ℝ) : Prop :=
  q k = 0 ∧ (∀ j < k, q (j + 1) ≤ q j) ∧
    (∀ y ∈ c.jumps, 0 < y → y < q 0 → ∃ j, 1 ≤ j ∧ j < k ∧ y = q j) ∧
    ∀ j < k, ∀ y, q (j + 1) < y → y < q j → y ∉ c.jumps → c.fn y = ht j

theorem IsRightLevels.congr_ht {c : BoundaryWord} {k : ℕ} {q ht ht' : ℕ → ℝ} (h : IsRightLevels c k q ht)
    (he : ∀ j < k, ht j = ht' j) : IsRightLevels c k q ht' :=
  ⟨h.1, h.2.1, h.2.2.1, fun j hj y h1 h2 h3 => (h.2.2.2 j hj y h1 h2 h3).trans (he j hj)⟩

theorem isRightLevels_zero (c : BoundaryWord) (ht : ℕ → ℝ) : IsRightLevels c 0 (fun _ => 0) ht :=
  ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j), fun _ _ h1 h2 => absurd (h1.trans h2) (lt_irrefl 0),
    fun j hj => absurd hj (Nat.not_lt_zero j)⟩

/-- **One more piece, right side** (mirror of `isLeftLevels_stopWord`): the right levels move by the record position
`R` of right marks, and the new piece's right side carries `λ − θχ`. -/
theorem isRightLevels_stopWord (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {k : ℕ} {q ht : ℕ → ℝ}
    (h : IsRightLevels c k q ht) :
    IsRightLevels (stopWord κ (c, θ, r)) (k + 1) (nextLev (markPos (rdrv r) (rtime r)) k q)
      (fun j => if j < k then ht j else sleLambda κ - θ * chiC κ) := by
  classical
  obtain ⟨hqk, hqm, hqJ, hqf⟩ := h
  set R := markPos (rdrv r) (rtime r) with hRdef
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hRm : ∀ {x x' : ℝ}, 0 ≤ x → x ≤ x' → R x ≤ R x' := fun hx hxx' => markPos_mono hw hw0 hT hx hxx'
  have hRn : ∀ {x : ℝ}, 0 ≤ x → 0 ≤ R x := fun hx => markPos_nonneg hw hw0 hT hx
  have hmono := ge_of_succ_ge' hqm
  have hq0 : ∀ j ≤ k, 0 ≤ q j := fun j hj => hqk ▸ hmono j k hj le_rfl
  set xR := flowLineXR c.fn c.jumps 0 with hxRdef
  have hxR : ∀ j, xR j = 0 ∨ (0 < xR j ∧ xR j ∈ c.jumps) := Restart.RetAux79.flowLineXR_eq_zero_or_mem c
  have hxRn : ∀ j, 0 ≤ xR j := fun j => by
    rcases hxR j with h0 | ⟨h0, -⟩
    · exact h0.ge
    · exact h0.le
  have hxL := Restart.RetAux79.flowLineXL_eq_zero_or_mem c
  have hmark : ∀ j, xR j < q 0 → xR j = 0 ∨ ∃ m, 1 ≤ m ∧ m < k ∧ xR j = q m := by
    intro j hj
    rcases hxR j with h0 | ⟨h0, hJ⟩
    · exact Or.inl h0
    · exact Or.inr (hqJ _ hJ h0 hj)
  refine ⟨nextLev_succ _ _ _, fun j hj => ?_, fun y hy h1 h2 => ?_, fun j hj x h1 h2 hxJ => ?_⟩
  · rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [nextLev_of_le hjk.le, nextLev_of_le hjk]
      exact hRm (hq0 _ hjk) (hqm j hjk)
    · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) hjk
      rw [nextLev_of_le le_rfl, nextLev_succ]
      exact hRn (hq0 _ le_rfl)
  · rw [nextLev_of_le (Nat.zero_le k)] at h2
    rcases mem_jumps_stopWord hy with ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩
    · have : markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i) ≤ 0 := by
        refine markPosL_nonpos hw hw0 hT ?_
        rcases hxL i with h0 | ⟨h0, -⟩
        · exact h0.le
        · exact h0.le
      linarith
    · exact absurd h1 (lt_irrefl 0)
    · have hqj : xR j < q 0 := by
        by_contra hle
        exact absurd (hRm (hq0 0 (Nat.zero_le k)) (not_lt.1 hle)) (not_le.2 h2)
      rcases hmark j hqj with h0 | ⟨m, hm1, hmk, hm⟩
      · have hk0 : k ≠ 0 := by
          rintro rfl
          rw [hqk] at hqj
          linarith [hxRn j]
        refine ⟨k, Nat.one_le_iff_ne_zero.2 hk0, Nat.lt_succ_self k, ?_⟩
        rw [nextLev_of_le le_rfl, hqk]
        show R (xR j) = R 0
        rw [h0]
      · refine ⟨m, hm1, Nat.lt_succ_of_lt hmk, ?_⟩
        rw [nextLev_of_le hmk.le]
        show R (xR j) = R (q m)
        rw [hm]
  · have hx0 : 0 < x := by
      refine lt_of_le_of_lt ?_ h1
      rcases Nat.lt_or_ge (j + 1) (k + 1) with hj1 | hj1
      · rw [nextLev_of_le (Nat.lt_succ_iff.1 hj1)]
        exact hRn (hq0 _ (Nat.lt_succ_iff.1 hj1))
      · rw [show j + 1 = k + 1 by omega, nextLev_succ]
    rw [fn_stopWord c θ r hxJ hx0.ne']
    unfold forceBoundaryData
    simp only [not_lt.2 hx0.le, ↓reduceIte]
    rcases Nat.lt_or_ge j k with hjk | hjk
    · rw [nextLev_of_le hjk] at h1
      rw [nextLev_of_le hjk.le] at h2
      have hlt : q (j + 1) < q j := by
        rcases (hqm j hjk).lt_or_eq with h | h
        · exact h
        · rw [h] at h1; exact absurd (h1.trans h2) (lt_irrefl _)
      set y := (q j + q (j + 1)) / 2 with hy
      have hy1 : q (j + 1) < y := by rw [hy]; linarith
      have hy2 : y < q j := by rw [hy]; linarith
      have hy0 : 0 < y := (hq0 _ hjk).trans_lt hy1
      have hqy : y < q 0 := hy2.trans_le (hmono 0 j (Nat.zero_le j) hjk.le)
      have hyJ : y ∉ c.jumps := by
        intro hyJ
        obtain ⟨m, -, hmk, hm⟩ := hqJ y hyJ hy0 hqy
        rcases Nat.lt_or_ge m (j + 1) with hmj | hmj
        · have := hmono m j (Nat.lt_succ_iff.1 hmj) hjk.le
          rw [← hm] at this; linarith
        · have := hmono (j + 1) m hmj hmk.le
          rw [← hm] at this; linarith
      have hfilt : (Finset.univ.filter fun i : Fin (flowLineNR c.fn c.jumps 0) => R (xR i) ≤ x) =
          Finset.univ.filter fun i => xR i ≤ y := by
        refine Finset.filter_congr fun i _ => ⟨fun hxi => ?_, fun hyi => ?_⟩
        · by_contra hle
          push Not at hle
          have hle' : q j ≤ xR i := by
            rcases hxR i with h0 | ⟨h0, hJ⟩
            · rw [h0] at hle; linarith
            · by_cases hp : q 0 ≤ xR i
              · exact (hmono 0 j (Nat.zero_le j) hjk.le).trans hp
              · obtain ⟨m, -, hmk, hm⟩ := hqJ _ hJ h0 (not_le.1 hp)
                rw [hm] at hle ⊢
                rcases Nat.lt_or_ge m (j + 1) with hmj | hmj
                · exact hmono m j (Nat.lt_succ_iff.1 hmj) hjk.le
                · have := hmono (j + 1) m hmj hmk.le; linarith
          have := hRm (hq0 _ hjk.le) hle'
          linarith
        · have hge : xR i ≤ q (j + 1) := by
            rcases hmark i (hyi.trans_lt hqy) with h0 | ⟨m, -, hmk, hm⟩
            · rw [h0]; exact hq0 _ hjk
            · rw [hm] at hyi ⊢
              rcases Nat.lt_or_ge m (j + 1) with hmj | hmj
              · have := hmono m j (Nat.lt_succ_iff.1 hmj) hjk.le; linarith
              · exact hmono (j + 1) m hmj hmk.le
          exact (hRm (hxRn i) hge).trans h1.le
      rw [hfilt]
      have hseed := Exist.forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 θ hy0.ne'
        (by rw [add_zero]; exact hyJ)
      unfold forceBoundaryData at hseed
      simp only [not_lt.2 hy0.le, ↓reduceIte] at hseed
      rw [add_zero, hqf j hjk y hy1 hy2 hyJ] at hseed
      simp only [hjk, ↓reduceIte]
      linarith
    · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) hjk
      rw [nextLev_of_le le_rfl, hqk] at h2
      have hempty : (Finset.univ.filter fun i : Fin (flowLineNR c.fn c.jumps 0) => R (xR i) ≤ x) = ∅ := by
        refine Finset.filter_false_of_mem fun i _ => not_le.2 ?_
        exact h2.trans_le (hRm le_rfl (hxRn i))
      rw [hempty, Finset.sum_empty, add_zero, mul_one]
      simp only [lt_irrefl, ↓reduceIte, sleLambda]

end Right

/-! ### The iterated stop word -/

section Iter

variable {κ : ℝ} (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ) (θ : ℕ → ℝ)

open Theorem14.GW2Schedule

/-- **The left levels read off records**: the record position of each record applied to the earlier levels. -/
def levL : (k : ℕ) → PastData k → ℕ → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun u => nextLev (markPosL (rdrv (u (Fin.last k))) (rtime (u (Fin.last k)))) k
      (levL k (Fin.init (α := fun _ => RecData) u))

/-- **The right levels read off records.** -/
def levR : (k : ℕ) → PastData k → ℕ → ℝ
  | 0 => fun _ _ => 0
  | k + 1 => fun u => nextLev (markPos (rdrv (u (Fin.last k))) (rtime (u (Fin.last k)))) k
      (levR k (Fin.init (α := fun _ => RecData) u))

/-- **The side heights of the iterated stop word, left**: after the pieces `0, …, k − 1` (records `u`), the word has the
left levels `levL k u` with the heights `−λ − θ_j χ`. -/
theorem isLeftLevels_pastWord (hκ : 0 < κ) :
    ∀ (k : ℕ) (u : PastData k), IsLeftLevels (pastWord (stopWord κ) c₀ x₀ θ k u) k (levL k u)
      (fun j => -sleLambda κ - θ j * chiC κ)
  | 0, _ => isLeftLevels_zero _ _
  | k + 1, u => by
    have ih := isLeftLevels_pastWord hκ k (Fin.init (α := fun _ => RecData) u)
    have h := isLeftLevels_stopWord hκ _ (θ k) (u (Fin.last k)) ih
    refine h.congr_ht fun j hj => ?_
    rcases Nat.lt_or_ge j k with hjk | hjk
    · simp only [hjk, ↓reduceIte]
    · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) hjk
      simp only [lt_irrefl, ↓reduceIte]

/-- **The side heights of the iterated stop word, right**: levels `levR k u`, heights `λ − θ_j χ`. -/
theorem isRightLevels_pastWord (hκ : 0 < κ) :
    ∀ (k : ℕ) (u : PastData k), IsRightLevels (pastWord (stopWord κ) c₀ x₀ θ k u) k (levR k u)
      (fun j => sleLambda κ - θ j * chiC κ)
  | 0, _ => isRightLevels_zero _ _
  | k + 1, u => by
    have ih := isRightLevels_pastWord hκ k (Fin.init (α := fun _ => RecData) u)
    have h := isRightLevels_stopWord hκ _ (θ k) (u (Fin.last k)) ih
    refine h.congr_ht fun j hj => ?_
    rcases Nat.lt_or_ge j k with hjk | hjk
    · simp only [hjk, ↓reduceIte]
    · obtain rfl : j = k := le_antisymm (Nat.lt_succ_iff.1 hj) hjk
      simp only [lt_irrefl, ↓reduceIte]

end Iter

end InteractingSLE.Sec5.CrossCond.StagedFinal
