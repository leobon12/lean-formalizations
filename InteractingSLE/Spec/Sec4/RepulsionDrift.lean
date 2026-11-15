/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.PartialSums
import InteractingSLE.Spec.Sec2.TerminalPath

/-!
# Aux. lemma 6, deterministic part: groups, partial sums and the repulsive drift

Packet PROVE-SEC4-A2. Specification §2.2, proof of Aux. lemma 6 (`source/spec/p001-048.md`,
(RP4)–(RP5)). For a side with ordered positions `x` (nondecreasing away from the seed) and weights
`ρ`, `HasGroupEndSums c ρ x` says that every partial sum ending at the last index of an initial
group of coincident marks is at least `c` (the source's "every partial sum on each nonempty side,
after amalgamation"). It follows from `HasAdmissiblePartialSums` on both sides
(`hasGroupEndSums_right`, `hasGroupEndSums_left`).

* `neg_two_lt_sum_collision`, `not_thresholdCondition_of_hasGroupEndSums`: a group colliding with
  the driver is a whole initial segment of groups, so its weight is at least `c > −2`;
* `le_sum_div_of_hasGroupEndSums` (RP4): for ordered positive gaps `d` which coincide on coincident
  marks, `∑ ρ_i/d_i ≥ c/d_1` (Abel summation; the signs of the individual weights do not matter);
* path facts for `IsIntegratedSLEPath`: coincident marks stay coincident
  (`IsIntegratedSLEPath.vR_eq_of_xR_eq`), and the gap `Y = V^{1,R} − W` satisfies (RP5)
  `Y_u = Y_s − √κ (B_u − B_s) + ∫_s^u β` with the explicit drift `rightGapDrift`, dominated by the
  monotone process `rightGapDom` and bounded below by `κ/(2Y) − C` when the left gaps are at
  least `a` (`IsIntegratedSLEPath.rightGapDrift_ge`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Finset Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec4

variable {n : ℕ}

/-- Every partial sum ending at the last index of an initial group of coincident marks is at least
`c`: for each `j` such that all later marks are strictly further out (`x j < x i` for `j < i`),
`c ≤ ∑_{i ≤ j} ρ_i`. Positions `x` are nondecreasing away from the seed (`x = xR`, or `x = −xL`). -/
def HasGroupEndSums (c : ℝ) {n : ℕ} (ρ x : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, (∀ i, j < i → x j < x i) → c ≤ ∑ i ∈ univ.filter (fun i => i ≤ j), ρ i

/-- The right side of an admissible word has admissible group-end sums. -/
theorem hasGroupEndSums_right {k : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (h : HasAdmissiblePartialSums k ρL ρR xL xR)
    (hmono : Monotone xR) (hnn : ∀ i, 0 ≤ xR i) : HasGroupEndSums (k / 2 - 2) ρR xR := by
  intro j hj
  have hset : univ.filter (fun i => xR i ≤ xR j) = univ.filter (fun i => i ≤ j) := by
    ext i
    simp only [mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun hi => ?_, fun hij => hmono hij⟩
    by_contra hij
    exact absurd hi (not_le.2 (hj i (not_le.1 hij)))
  rw [← hset]
  exact h.2 (xR j) (hnn j) ⟨j, le_rfl⟩

/-- The left side of an admissible word has admissible group-end sums (positions `−xL`). -/
theorem hasGroupEndSums_left {k : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (h : HasAdmissiblePartialSums k ρL ρR xL xR)
    (hanti : Antitone xL) (hnp : ∀ i, xL i ≤ 0) : HasGroupEndSums (k / 2 - 2) ρL (-xL) := by
  intro j hj
  simp only [Pi.neg_apply, neg_lt_neg_iff] at hj
  obtain ⟨x, hx0, hxset⟩ : ∃ x < 0,
      univ.filter (fun i => x < xL i) = univ.filter (fun i => i ≤ j) := by
    by_cases hlast : j.1 + 1 < nL
    · set j' : Fin nL := ⟨j.1 + 1, hlast⟩
      have hjj' : j < j' := Fin.lt_def.2 (Nat.lt_succ_self _)
      have hlt : xL j' < xL j := hj j' hjj'
      refine ⟨xL j', hlt.trans_le (hnp j), ?_⟩
      ext i
      simp only [mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun hi => ?_, fun hij => hlt.trans_le (hanti hij)⟩
      by_contra hij
      have : j' ≤ i := Fin.le_def.2 (by
        have := Fin.lt_def.1 (not_le.1 hij); simp only [j']; omega)
      exact absurd (hanti this) (not_le.2 hi)
    · refine ⟨xL j - 1, by linarith [hnp j], ?_⟩
      ext i
      simp only [mem_filter, Finset.mem_univ, true_and]
      have hij : i ≤ j := Fin.le_def.2 (by have := i.2; omega)
      exact ⟨fun _ => hij, fun _ => by linarith [hanti hij]⟩
  rw [← hxset]
  have hjmem : j ∈ univ.filter (fun i => x < xL i) := by rw [hxset]; simp
  exact h.1 x hx0 ⟨j, (mem_filter.1 hjmem).2⟩

/-- **A colliding group is a whole union of initial groups**, so its weight exceeds `−2`: for a
side with nondecreasing positions `x`, nondecreasing current positions `v₀ ≥ w₀`, and `v₀`
constant on coincident marks, `−2 < ∑_{v₀ i = w₀} ρ_i`. -/
theorem neg_two_lt_sum_collision {c : ℝ} (hc : -2 < c) {ρ x v₀ : Fin n → ℝ} {w₀ : ℝ}
    (hx : Monotone x) (hadm : HasGroupEndSums c ρ x) (hv : Monotone v₀) (hwv : ∀ i, w₀ ≤ v₀ i)
    (hco : ∀ i j, x i = x j → v₀ i = v₀ j) :
    -2 < ∑ i ∈ univ.filter (fun i => v₀ i = w₀), ρ i := by
  set S := univ.filter (fun i => v₀ i = w₀)
  by_cases hS : S.Nonempty
  · set j := S.max' hS
    have hjS : j ∈ S := S.max'_mem hS
    have hj : v₀ j = w₀ := (mem_filter.1 hjS).2
    have hSeq : S = univ.filter (fun i => i ≤ j) := by
      ext i
      simp only [S, mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun hi => S.le_max' i (by simp [S, hi]), fun hij => ?_⟩
      exact le_antisymm ((hv hij).trans hj.le) (hwv i)
    have hend : ∀ i, j < i → x j < x i := by
      intro i hji
      refine lt_of_le_of_ne (hx hji.le) fun heq => ?_
      have hiS : i ∈ S := by simp only [S, mem_filter, Finset.mem_univ, true_and]; rw [← hco j i heq, hj]
      exact absurd (S.le_max' i hiS) (not_le.2 hji)
    rw [hSeq]
    exact hc.trans_le (hadm j hend)
  · rw [Finset.not_nonempty_iff_eq_empty.1 hS, sum_empty]
    norm_num

/-- **No threshold at an ordered state of an admissible word**: if both sides have group-end sums
at least `c > −2`, the current positions are ordered and constant on coincident marks, then the
continuation-threshold condition fails. -/
theorem not_thresholdCondition_of_hasGroupEndSums {c : ℝ} (hc : -2 < c) {nL nR : ℕ}
    {ρL xL vL₀ : Fin nL → ℝ} {ρR xR vR₀ : Fin nR → ℝ} {w₀ : ℝ} (hxL : Antitone xL)
    (hxR : Monotone xR) (hL : HasGroupEndSums c ρL (-xL)) (hR : HasGroupEndSums c ρR xR)
    (hvL : Antitone vL₀) (hvR : Monotone vR₀) (hLw : ∀ i, vL₀ i ≤ w₀) (hwR : ∀ i, w₀ ≤ vR₀ i)
    (hcoL : ∀ i j, xL i = xL j → vL₀ i = vL₀ j) (hcoR : ∀ i j, xR i = xR j → vR₀ i = vR₀ j) :
    ¬ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀ := by
  unfold ForceWord.ThresholdCondition
  push Not
  refine ⟨?_, neg_two_lt_sum_collision hc hxR hR hvR hwR hcoR⟩
  have h := neg_two_lt_sum_collision (v₀ := -vL₀) (w₀ := -w₀) hc (fun i j hij => neg_le_neg (hxL hij))
    hL (fun i j hij => neg_le_neg (hvL hij)) (fun i => neg_le_neg (hLw i))
    (fun i j hij => by simp only [Pi.neg_apply, neg_inj] at hij ⊢; exact hcoL i j hij)
  simpa only [Pi.neg_apply, neg_inj] using h

/-! ### (RP4): Abel summation -/

/-- Abel summation in the form used for (RP4). -/
theorem sum_mul_eq_abel (ρ e : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ range m, ρ k * e k =
      ∑ k ∈ range m, (∑ i ∈ range (k + 1), ρ i) * (e k - e (k + 1)) +
        (∑ i ∈ range m, ρ i) * e m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ (fun k => (∑ i ∈ range (k + 1), ρ i) * (e k - e (k + 1))),
      sum_range_succ ρ m]
    ring

/-- **(RP4) for sequences**: for positive nondecreasing gaps `d_0 ≤ ⋯ ≤ d_{m−1}` and weights whose
partial sums `∑_{i ≤ k} ρ_i` are at least `c` except where `d_k = d_{k+1}`,
`c/d_0 ≤ ∑_{k < m} ρ_k/d_k`. -/
theorem le_sum_div_of_partialSums {m : ℕ} {ρ d : ℕ → ℝ} {c : ℝ} (hm : 0 < m)
    (hpos : ∀ k < m, 0 < d k) (hmono : ∀ k, k + 1 < m → d k ≤ d (k + 1))
    (hgrp : ∀ k < m, (k + 1 < m ∧ d k = d (k + 1)) ∨ c ≤ ∑ i ∈ range (k + 1), ρ i) :
    c / d 0 ≤ ∑ k ∈ range m, ρ k / d k := by
  set e : ℕ → ℝ := fun k => if k < m then 1 / d k else 0 with he
  have hsum : ∑ k ∈ range m, ρ k / d k = ∑ k ∈ range m, ρ k * e k := by
    refine sum_congr rfl fun k hk => ?_
    simp only [he, Finset.mem_range.1 hk, ↓reduceIte]
    ring
  have hem : e m = 0 := by simp [he]
  rw [hsum, sum_mul_eq_abel, hem, mul_zero, add_zero]
  have hterm : ∀ k ∈ range m, c * (e k - e (k + 1)) ≤
      (∑ i ∈ range (k + 1), ρ i) * (e k - e (k + 1)) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hδ : 0 ≤ e k - e (k + 1) := by
      by_cases hk1 : k + 1 < m
      · simp only [he, hk', hk1, ↓reduceIte, sub_nonneg]
        exact one_div_le_one_div_of_le (hpos k hk') (hmono k hk1)
      · simp only [he, hk', hk1, ↓reduceIte, sub_zero]; exact (one_div_pos.2 (hpos k hk')).le
    rcases hgrp k hk' with ⟨hk1, hdk⟩ | hS
    · have : e k - e (k + 1) = 0 := by simp only [he, hk', hk1, ↓reduceIte, hdk, sub_self]
      rw [this, mul_zero, mul_zero]
    · exact mul_le_mul_of_nonneg_right hS hδ
  refine le_trans (le_of_eq ?_) (sum_le_sum hterm)
  rw [← mul_sum, sum_range_sub' e m, hem, sub_zero]
  simp only [he, hm, ↓reduceIte]
  ring

/-- Prefix sums over `Fin n` as sums over `range`. -/
theorem sum_filter_le_eq_sum_range (ρ : Fin n → ℝ) (j : Fin n) :
    ∑ i ∈ univ.filter (fun i => i ≤ j), ρ i =
      ∑ k ∈ range (j.1 + 1), (if h : k < n then ρ ⟨k, h⟩ else 0) := by
  rw [sum_filter]
  have h1 : ∑ i : Fin n, (if i ≤ j then ρ i else 0) =
      ∑ i : Fin n, (fun k : ℕ => if k ≤ j.1 then (if h : k < n then ρ ⟨k, h⟩ else 0) else 0) i := by
    refine sum_congr rfl fun i _ => ?_
    simp only [Fin.le_def, i.2, ↓reduceDIte, Fin.eta]
  rw [h1, Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    if k ≤ j.1 then (if h : k < n then ρ ⟨k, h⟩ else 0) else 0) n, ← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, Finset.mem_range]
  have := j.2
  omega

/-- **(RP4)**: for a side with nondecreasing positions `x` and admissible group-end sums, and gaps
`d` that are positive, nondecreasing and equal on coincident marks,
`c/d_1 ≤ ∑_i ρ_i/d_i`. -/
theorem le_sum_div_of_hasGroupEndSums (hn : 0 < n) {ρ x d : Fin n → ℝ} {c : ℝ}
    (hx : Monotone x) (hadm : HasGroupEndSums c ρ x) (hd : Monotone d) (hpos : ∀ i, 0 < d i)
    (hco : ∀ i j, x i = x j → d i = d j) : c / d ⟨0, hn⟩ ≤ ∑ i, ρ i / d i := by
  set ρ' : ℕ → ℝ := fun k => if h : k < n then ρ ⟨k, h⟩ else 0 with hρ'
  set d' : ℕ → ℝ := fun k => if h : k < n then d ⟨k, h⟩ else 1 with hd'
  have hsum : ∑ i, ρ i / d i = ∑ k ∈ range n, ρ' k / d' k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ρ' k / d' k) n]
    refine sum_congr rfl fun i _ => ?_
    simp only [hρ', hd', i.2, ↓reduceDIte, Fin.eta]
  have hd0 : d' 0 = d ⟨0, hn⟩ := by simp only [hd', hn, ↓reduceDIte]
  rw [hsum, ← hd0]
  refine le_sum_div_of_partialSums hn (fun k hk => ?_) (fun k hk => ?_) (fun k hk => ?_)
  · simp only [hd', hk, ↓reduceDIte]; exact hpos _
  · simp only [hd', hk, Nat.lt_of_succ_lt hk, ↓reduceDIte]
    exact hd (Fin.le_def.2 (Nat.le_succ k))
  · set j : Fin n := ⟨k, hk⟩
    by_cases hend : ∀ i, j < i → x j < x i
    · right
      rw [← sum_filter_le_eq_sum_range ρ j]
      exact hadm j hend
    · left
      push Not at hend
      obtain ⟨i, hji, hxi⟩ := hend
      have hk1 : k + 1 < n := by have := Fin.lt_def.1 hji; have := i.2; simp only [j] at *; omega
      set j' : Fin n := ⟨k + 1, hk1⟩
      have hjj' : j ≤ j' := Fin.le_def.2 (Nat.le_succ k)
      have hj'i : j' ≤ i := Fin.le_def.2 (by
        have := Fin.lt_def.1 hji; simp only [j, j'] at *; omega)
      have hxeq : x j = x j' := le_antisymm (hx hjj') ((hx hj'i).trans hxi)
      refine ⟨hk1, ?_⟩
      simp only [hd', hk, hk1, ↓reduceDIte]
      exact hco j j' hxeq

/-! ### The gap to the nearest right mark -/

/-- The drift of the gap `Y = V^{i₀,R} − W` in (RP5):
`2/(V^{i₀,R} − W) − (∑ ρ^{i,L}/(W − V^{i,L}) + ∑ ρ^{i,R}/(W − V^{i,R}))`. -/
def rightGapDrift {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nR) (p : ℝ≥0) : ℝ :=
  2 / (vR i₀ p - w p) - (∑ i, ρL i / (w p - vL i p) + ∑ i, ρR i / (w p - vR i p))

/-- A monotone process dominating `∫ |rightGapDrift|`:
`V^{i₀,R} + ∑ |ρ^{i,R}|/2 · V^{i,R} − ∑ |ρ^{i,L}|/2 · V^{i,L}`. -/
def rightGapDom {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nR) (p : ℝ≥0) : ℝ :=
  vR i₀ p + ∑ i, |ρR i| / 2 * vR i p - ∑ i, |ρL i| / 2 * vL i p

theorem intervalIntegrable_of_le_of_zero {f : ℝ → ℝ} {s u : ℝ≥0} (hsu : s ≤ u)
    (hf : IntervalIntegrable f volume 0 u) : IntervalIntegrable f volume s u :=
  hf.mono_set (by
    rw [uIcc_of_le (by exact_mod_cast hsu : (s : ℝ) ≤ u), uIcc_of_le (NNReal.coe_nonneg u)]
    exact Icc_subset_Icc (NNReal.coe_nonneg s) le_rfl)

theorem abs_div_eq_half_mul (ρ x : ℝ) (hx : 0 ≤ x) : |ρ / x| = |ρ| / 2 * (2 / x) := by
  rw [abs_div, abs_of_nonneg hx]; ring

end Sec4

namespace IsIntegratedSLEPath

open Sec4

variable {k : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

section

variable (h : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ)
include h

/-- Coincident right marks stay coincident. -/
theorem vR_eq_of_xR_eq {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {i j : Fin nR} (hij : xR i = xR j) :
    vR i t = vR j t := by
  rcases le_total i j with hle | hle
  · have h1 := h.isForcePath.vR_sub_vR_le ht hle
    have h2 := h.isForcePath.monotone_vR ht hle
    linarith
  · have h1 := h.isForcePath.vR_sub_vR_le ht hle
    have h2 := h.isForcePath.monotone_vR ht hle
    linarith

/-- Coincident left marks stay coincident. -/
theorem vL_eq_of_xL_eq {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {i j : Fin nL} (hij : xL i = xL j) :
    vL i t = vL j t := by
  rcases le_total i j with hle | hle
  · have h1 := h.isForcePath.vL_sub_vL_le ht hle
    have h2 := h.isForcePath.antitone_vL ht hle
    linarith
  · have h1 := h.isForcePath.vL_sub_vL_le ht hle
    have h2 := h.isForcePath.antitone_vL ht hle
    linarith

theorem intervalIntegrable_rightGapDrift (i₀ : Fin nR) {s u : ℝ≥0} (hsu : s ≤ u)
    (hu : (u : ℝ≥0∞) < ζ) :
    IntervalIntegrable (fun r : ℝ => rightGapDrift ρL ρR w vL vR i₀ r.toNNReal) volume s u :=
  intervalIntegrable_of_le_of_zero hsu ((h.isForcePath.intervalIntegrable_forceR hu i₀).sub
    (h.isForcePath.intervalIntegrable_driverDrift hu))

/-- **(RP5)**: `Y_u = Y_s − √κ (B_u − B_s) + ∫_s^u β` for the gap `Y = V^{i₀,R} − W`. -/
theorem gap_eq (i₀ : Fin nR) {s u : ℝ≥0} (hsu : s ≤ u) (hu : (u : ℝ≥0∞) < ζ) :
    vR i₀ u - w u = vR i₀ s - w s + -Real.sqrt k * (b u - b s) +
      ∫ r in (s : ℝ)..u, rightGapDrift ρL ρR w vL vR i₀ r.toNNReal := by
  have h1 := h.isForcePath.vR_sub hsu hu i₀
  have h2 := h.isForcePath.w_sub h.driverEq hsu hu
  have hI1 := intervalIntegrable_of_le_of_zero hsu (h.isForcePath.intervalIntegrable_forceR hu i₀)
  have hI2 := intervalIntegrable_of_le_of_zero hsu (h.isForcePath.intervalIntegrable_driverDrift hu)
  have h3 : ∫ r in (s : ℝ)..u, rightGapDrift ρL ρR w vL vR i₀ r.toNNReal =
      (∫ r in (s : ℝ)..u, 2 / (vR i₀ r.toNNReal - w r.toNNReal)) -
        ∫ r in (s : ℝ)..u, Sec2.driverDrift ρL ρR w vL vR r :=
    intervalIntegral.integral_sub hI1 hI2
  rw [h3]
  linarith

/-- **Domination of the drift**: `∫_s^u |β| ≤ ψ_u − ψ_s` for `ψ = rightGapDom`. -/
theorem integral_abs_rightGapDrift_le (i₀ : Fin nR) {s u : ℝ≥0} (hsu : s ≤ u)
    (hu : (u : ℝ≥0∞) < ζ) :
    ∫ r in (s : ℝ)..u, |rightGapDrift ρL ρR w vL vR i₀ r.toNNReal| ≤
      rightGapDom ρL ρR vL vR i₀ u - rightGapDom ρL ρR vL vR i₀ s := by
  have hp := h.isForcePath
  have hsu' : (s : ℝ) ≤ u := by exact_mod_cast hsu
  have iR : ∀ i, IntervalIntegrable (fun r : ℝ => 2 / (vR i r.toNNReal - w r.toNNReal))
      volume s u := fun i => intervalIntegrable_of_le_of_zero hsu (hp.intervalIntegrable_forceR hu i)
  have iL : ∀ i, IntervalIntegrable (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal))
      volume s u := fun i => intervalIntegrable_of_le_of_zero hsu (hp.intervalIntegrable_forceL hu i)
  set g : ℝ → ℝ := fun r => 2 / (vR i₀ r.toNNReal - w r.toNNReal) +
    ∑ i, |ρL i| / 2 * -(2 / (vL i r.toNNReal - w r.toNNReal)) +
    ∑ i, |ρR i| / 2 * (2 / (vR i r.toNNReal - w r.toNNReal)) with hg
  have iL' : ∀ i, IntervalIntegrable (fun r : ℝ => -(2 / (vL i r.toNNReal - w r.toNNReal)))
      volume s u := fun i => (iL i).neg
  have igL : IntervalIntegrable (fun r : ℝ => ∑ i, |ρL i| / 2 *
      -(2 / (vL i r.toNNReal - w r.toNNReal))) volume s u := by
    have := IntervalIntegrable.sum Finset.univ fun i _ => (iL' i).const_mul (|ρL i| / 2)
    simpa only [Finset.sum_fn] using this
  have igR : IntervalIntegrable (fun r : ℝ => ∑ i, |ρR i| / 2 *
      (2 / (vR i r.toNNReal - w r.toNNReal))) volume s u := by
    have := IntervalIntegrable.sum Finset.univ fun i _ => (iR i).const_mul (|ρR i| / 2)
    simpa only [Finset.sum_fn] using this
  have ig : IntervalIntegrable g volume s u := ((iR i₀).add igL).add igR
  have hint : ∫ r in (s : ℝ)..u, g r =
      rightGapDom ρL ρR vL vR i₀ u - rightGapDom ρL ρR vL vR i₀ s := by
    rw [hg, intervalIntegral.integral_add ((iR i₀).add igL) igR,
      intervalIntegral.integral_add (iR i₀) igL,
      intervalIntegral.integral_finsetSum fun i _ => (iL' i).const_mul (|ρL i| / 2),
      intervalIntegral.integral_finsetSum fun i _ => (iR i).const_mul (|ρR i| / 2)]
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg]
    rw [← hp.vR_sub hsu hu i₀]
    simp only [← hp.vL_sub hsu hu, ← hp.vR_sub hsu hu, rightGapDom]
    simp only [mul_sub, mul_neg, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  rw [← hint]
  refine intervalIntegral.integral_mono_on hsu' (intervalIntegrable_rightGapDrift h i₀ hsu hu).abs
    ig fun r hr => ?_
  have hr0 : r ∈ Icc (0 : ℝ) u := ⟨(NNReal.coe_nonneg s).trans hr.1, hr.2⟩
  have hlt := Sec2.toNNReal_lt_of_mem_Icc hu hr0
  set p := r.toNNReal
  have hR0 : 0 ≤ vR i₀ p - w p := sub_nonneg.2 (hp.w_le_vR hlt i₀)
  have h1 : |2 / (vR i₀ p - w p)| = 2 / (vR i₀ p - w p) :=
    abs_of_nonneg (div_nonneg (by norm_num) hR0)
  have h2 : |∑ i, ρL i / (w p - vL i p)| ≤
      ∑ i, |ρL i| / 2 * -(2 / (vL i p - w p)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [abs_div_eq_half_mul _ _ (sub_nonneg.2 (hp.vL_le_w hlt i)), ← neg_sub (vL i p), div_neg]
  have h3 : |∑ i, ρR i / (w p - vR i p)| ≤ ∑ i, |ρR i| / 2 * (2 / (vR i p - w p)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [← neg_sub (vR i p), div_neg, abs_neg,
      abs_div_eq_half_mul _ _ (sub_nonneg.2 (hp.w_le_vR hlt i))]
  have h4 := abs_sub (2 / (vR i₀ p - w p)) (∑ i, ρL i / (w p - vL i p) + ∑ i, ρR i / (w p - vR i p))
  have h5 := abs_add_le (∑ i, ρL i / (w p - vL i p)) (∑ i, ρR i / (w p - vR i p))
  show |rightGapDrift ρL ρR w vL vR i₀ p| ≤ g r
  simp only [rightGapDrift, hg]
  linarith

/-- **(RP4)–(RP5), the drift inequality**: if the right group-end sums are at least
`c = κ/2 − 2`, the nearest right gap `Y` is positive and every left gap is at least `a > 0`, then
`β ≥ κ/(2Y) − C` with `C = ∑ |ρ^{i,L}|/a`. -/
theorem rightGapDrift_ge (hnR : 0 < nR) (hxR : Monotone xR)
    (hadm : HasGroupEndSums (k / 2 - 2) ρR xR) {p : ℝ≥0} (hp : (p : ℝ≥0∞) < ζ) {a : ℝ}
    (ha : 0 < a) (hY : 0 < vR ⟨0, hnR⟩ p - w p) (hL : ∀ i, a ≤ w p - vL i p) :
    k / (2 * (vR ⟨0, hnR⟩ p - w p)) - (∑ i, |ρL i|) / a ≤
      rightGapDrift ρL ρR w vL vR ⟨0, hnR⟩ p := by
  have hfp := h.isForcePath
  set Y := vR ⟨0, hnR⟩ p - w p
  have hdpos : ∀ i, 0 < vR i p - w p := fun i => by
    have : vR ⟨0, hnR⟩ p ≤ vR i p := hfp.monotone_vR hp (Fin.le_def.2 (Nat.zero_le _))
    linarith
  have hRP4 := le_sum_div_of_hasGroupEndSums hnR hxR hadm (d := fun i => vR i p - w p)
    (fun i j hij => by linarith [hfp.monotone_vR hp hij]) hdpos
    (fun i j hij => by rw [h.vR_eq_of_xR_eq hp hij])
  have hRsum : ∑ i, ρR i / (w p - vR i p) = -∑ i, ρR i / (vR i p - w p) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [← neg_sub (vR i p), div_neg]
  have hLsum : ∑ i, ρL i / (w p - vL i p) ≤ (∑ i, |ρL i|) / a := by
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun i _ => ?_
    have hgap : 0 < w p - vL i p := ha.trans_le (hL i)
    calc ρL i / (w p - vL i p) ≤ |ρL i| / (w p - vL i p) :=
          div_le_div_of_nonneg_right (le_abs_self _) hgap.le
      _ ≤ |ρL i| / a := div_le_div_of_nonneg_left (abs_nonneg _) ha (hL i)
  unfold rightGapDrift
  rw [hRsum]
  have hsplit : k / (2 * Y) = 2 / Y + (k / 2 - 2) / Y := by
    field_simp; ring
  rw [hsplit]
  linarith

end

end IsIntegratedSLEPath

end InteractingSLE
