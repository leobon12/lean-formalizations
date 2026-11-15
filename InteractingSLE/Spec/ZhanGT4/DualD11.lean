/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Lattice

/-!
# Zhan's A.1.4: patching finitely many stopped rectangles, (D11)

Packet PROVE-ZHAN-GT4-A12. Astra, *Follow-up proofs*, §A.1.4 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L363–L407, R38): finitely many protected rectangles `[0, S₁ₘ] × [0, S₂ₘ]`; with the non-dominated corners
`(a₁, b₁), …, (a_N, b_N)`, `a` increasing, `b` decreasing, `a₀ = b_{N+1} = 0`, for `a_{i−1} ≤ s ≤ a_i`,
`b_{j+1} ≤ t ≤ b_j`, `M*(s, t) = M(s, t)` if `i ≤ j`, and otherwise

  `M*(s, t) = M(a_j, t) M(s, b_i) ∏_{k=j+1}^{i−1} M(a_k, b_k) / ∏_{k=j}^{i−1} M(a_k, b_{k+1})`.   (D11)

"Axis values of `M` are one … Hence `M*` is continuous, equals `M` on every rectangle, equals one on both axes, and is
bounded above and below by deterministic positive constants, by (D9)."

## The closed form used here

Write `C = {S₁ₘ}` (the column ends), `prev c` the largest element of `C ∪ {0}` below `c`, and `h c = max{S₂ₘ : c ≤ S₁ₘ}`
(the staircase height over the column `[prev c, c]`). Then, with `m = log M`,

  `log M*(s, t) = ∑_{c ∈ C} (m(c ∧ s, h c ∧ t) − m(prev c ∧ s, h c ∧ t))`   (`patchLog`).

On the cell `a_{i−1} ≤ s ≤ a_i`, `b_{j+1} ≤ t ≤ b_j` this is exactly (D11): the columns `k ≤ j` telescope to `M(a_j, t)`,
the columns `j < k < i` give `M(a_k, b_k)/M(a_{k−1}, b_k)`, the column `i` gives `M(s, b_i)/M(a_{i−1}, b_i)`, the others
give `1` (dominated rectangles only repeat column ends). It needs no sorting and no tie-break, and every argument of `m`
lies in the staircase `⋃ₘ [0, S₁ₘ] × [0, S₂ₘ]` (`InStair`).

## Main results

* `patchLog_eq_of_inStair`: `M* = M` on every rectangle (given `m(0, ·) = 0`);
* `patchLog_zero_left`, `patchLog_zero_right`: `M* = 1` on both axes;
* `abs_patchLog_le`, `continuousOn_patchLog`: the bounds and continuity, from those of `m` on the staircase;
* `patchLog_column`: **the adapted structure** behind (D12): for `s ∈ [prev c, c]`,
  `log M*(s, t) − log M*(prev c, t) = m(s, h c ∧ t) − m(prev c, h c ∧ t)`, and `patchLog_of_maxIn_le`: constant after
  the last column; `stairH_eq_of_prevIn_lt`, `minGt_eq`: the column end and its height are determined by the
  rectangles not yet exited at `prev c`;
* `patchLog_symm`: **reflection**: the construction with the coordinates exchanged gives the same function, so the
  same column structure holds in `t` (`patchLog_column` applied to the transposed data);
* `patch`, the multiplicative form, with `patch_eq_of_inStair`, `patch_zero_left/right`, the bounds `patch_mem_Icc`,
  `continuousOn_patch`, `patch_column`.
-/

set_option autoImplicit false

noncomputable section

open Finset Set

namespace InteractingSLE.ZhanGT4

/-! ### Previous element and telescoping over a finite set of reals -/

/-- The largest element of `C ∪ {0}` strictly below `c` (or `0`). -/
def prevIn (C : Finset ℝ) (c : ℝ) : ℝ :=
  (insert 0 (C.filter (· < c))).max' (insert_nonempty _ _)

/-- The largest element of `C ∪ {0}`. -/
def maxIn (C : Finset ℝ) : ℝ :=
  (insert 0 C).max' (insert_nonempty _ _)

theorem prevIn_nonneg (C : Finset ℝ) (c : ℝ) : 0 ≤ prevIn C c :=
  le_max' _ _ (mem_insert_self _ _)

theorem le_prevIn {C : Finset ℝ} {c x : ℝ} (hx : x ∈ C) (hxc : x < c) : x ≤ prevIn C c :=
  le_max' _ _ (mem_insert_of_mem (mem_filter.2 ⟨hx, hxc⟩))

theorem prevIn_le {C : Finset ℝ} {c : ℝ} (hc : 0 ≤ c) : prevIn C c ≤ c := by
  refine max'_le _ _ _ fun y hy => ?_
  rcases mem_insert.1 hy with rfl | hy
  · exact hc
  · exact (mem_filter.1 hy).2.le

theorem prevIn_mem_or_eq_zero (C : Finset ℝ) (c : ℝ) : prevIn C c = 0 ∨ (prevIn C c ∈ C ∧ prevIn C c < c) := by
  have h : prevIn C c ∈ insert 0 (C.filter (· < c)) := max'_mem _ _
  rcases mem_insert.1 h with h | h
  · exact Or.inl h
  · exact Or.inr (mem_filter.1 h)

theorem prevIn_lt {C : Finset ℝ} {c : ℝ} (hc : 0 < c) : prevIn C c < c := by
  rcases prevIn_mem_or_eq_zero C c with h | h
  · rw [h]; exact hc
  · exact h.2

theorem maxIn_nonneg (C : Finset ℝ) : 0 ≤ maxIn C := le_max' _ _ (mem_insert_self _ _)

theorem le_maxIn {C : Finset ℝ} {x : ℝ} (hx : x ∈ C) : x ≤ maxIn C := le_max' _ _ (mem_insert_of_mem hx)

theorem prevIn_insert_of_le {C : Finset ℝ} {a c : ℝ} (hca : c ≤ a) : prevIn (insert a C) c = prevIn C c := by
  unfold prevIn
  congr 1
  rw [filter_insert, ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 hca))]

theorem prevIn_insert_self {C : Finset ℝ} {a : ℝ} (ha : ∀ x ∈ C, x < a) : prevIn (insert a C) a = maxIn C := by
  unfold prevIn maxIn
  congr 1
  rw [filter_insert, ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl a)), filter_true_of_mem ha]

theorem maxIn_insert {C : Finset ℝ} {a : ℝ} (ha0 : 0 ≤ a) (ha : ∀ x ∈ C, x < a) : maxIn (insert a C) = a := by
  refine le_antisymm (max'_le _ _ _ fun y hy => ?_) (le_max' _ _ (mem_insert_of_mem (mem_insert_self _ _)))
  rcases mem_insert.1 hy with rfl | hy
  · exact ha0
  rcases mem_insert.1 hy with rfl | hy
  · exact le_rfl
  · exact (ha y hy).le

theorem maxIn_empty : maxIn ∅ = 0 := by simp [maxIn]

/-- **Telescoping along `C ∪ {0}`**: `∑_{c ∈ C} (F c − F (prev c)) = F (max C) − F 0` for a finite set of
nonnegative reals. -/
theorem sum_sub_prevIn (C : Finset ℝ) (hC : ∀ c ∈ C, 0 ≤ c) (F : ℝ → ℝ) :
    ∑ c ∈ C, (F c - F (prevIn C c)) = F (maxIn C) - F 0 := by
  revert hC
  refine Finset.induction_on_max C (fun _ => by simp [maxIn_empty]) fun a C ha ih hC => ?_
  have haC : a ∉ C := fun h => lt_irrefl a (ha a h)
  have hC' : ∀ c ∈ C, 0 ≤ c := fun c hc => hC c (mem_insert_of_mem hc)
  rw [sum_insert haC, prevIn_insert_self ha, maxIn_insert (hC a (mem_insert_self _ _)) ha]
  have hrest : ∑ c ∈ C, (F c - F (prevIn (insert a C) c)) = ∑ c ∈ C, (F c - F (prevIn C c)) :=
    sum_congr rfl fun c hc => by rw [prevIn_insert_of_le (ha c hc).le]
  rw [hrest, ih hC']
  ring

/-! ### The staircase and its columns -/

variable {ι : Type*} [Fintype ι]

/-- The column ends `{S₁ m}`. -/
def stairCols (S₁ : ι → ℝ) : Finset ℝ := univ.image S₁

/-- The height of the staircase over the column ending at `c`: `max{S₂ m : c ≤ S₁ m}` (or `0`). -/
def stairH (S₁ S₂ : ι → ℝ) (c : ℝ) : ℝ :=
  (insert 0 ((univ.filter fun i => c ≤ S₁ i).image S₂)).max' (insert_nonempty _ _)

/-- A point lies under one of the rectangles `[0, S₁ m] × [0, S₂ m]`. -/
def InStair (S₁ S₂ : ι → ℝ) (x y : ℝ) : Prop := ∃ i, x ≤ S₁ i ∧ y ≤ S₂ i

/-- **The patched density, (D11), in log form.** -/
def patchLog (S₁ S₂ : ι → ℝ) (m : ℝ → ℝ → ℝ) (s t : ℝ) : ℝ :=
  ∑ c ∈ stairCols S₁, (m (min c s) (min (stairH S₁ S₂ c) t) - m (min (prevIn (stairCols S₁) c) s)
    (min (stairH S₁ S₂ c) t))

variable {S₁ S₂ : ι → ℝ}

theorem mem_stairCols (i : ι) : S₁ i ∈ stairCols S₁ := mem_image_of_mem _ (mem_univ _)

theorem nonneg_of_mem_stairCols (hS₁ : ∀ i, 0 ≤ S₁ i) {c : ℝ} (hc : c ∈ stairCols S₁) : 0 ≤ c := by
  obtain ⟨i, -, rfl⟩ := mem_image.1 hc
  exact hS₁ i

theorem stairH_nonneg (c : ℝ) : 0 ≤ stairH S₁ S₂ c := le_max' _ _ (mem_insert_self _ _)

theorem le_stairH {c : ℝ} {i : ι} (hi : c ≤ S₁ i) : S₂ i ≤ stairH S₁ S₂ c :=
  le_max' _ _ (mem_insert_of_mem (mem_image_of_mem S₂ (mem_filter.2 ⟨mem_univ i, hi⟩)))

/-- The height of a column is attained by a rectangle reaching over the column. -/
theorem exists_stairH_le (hS₂ : ∀ i, 0 ≤ S₂ i) {c : ℝ} (hc : c ∈ stairCols S₁) :
    ∃ i, c ≤ S₁ i ∧ stairH S₁ S₂ c ≤ S₂ i := by
  obtain ⟨j, -, rfl⟩ := mem_image.1 hc
  have h : stairH S₁ S₂ (S₁ j) ∈ insert 0 ((univ.filter fun i => S₁ j ≤ S₁ i).image S₂) := max'_mem _ _
  rcases mem_insert.1 h with h | h
  · exact ⟨j, le_rfl, h ▸ hS₂ j⟩
  · obtain ⟨i, hi, he⟩ := mem_image.1 h
    exact ⟨i, (mem_filter.1 hi).2, he.symm.le⟩

/-- Every argument of `m` in `patchLog` lies in the staircase. -/
theorem inStair_args (hS₂ : ∀ i, 0 ≤ S₂ i) {c : ℝ} (hc : c ∈ stairCols S₁) (hc0 : 0 ≤ c) (s t : ℝ) :
    InStair S₁ S₂ (min c s) (min (stairH S₁ S₂ c) t) ∧
      InStair S₁ S₂ (min (prevIn (stairCols S₁) c) s) (min (stairH S₁ S₂ c) t) := by
  obtain ⟨i, hci, hhi⟩ := exists_stairH_le (S₁ := S₁) hS₂ hc
  exact ⟨⟨i, (min_le_left _ _).trans hci, (min_le_left _ _).trans hhi⟩,
    ⟨i, (min_le_left _ _).trans ((prevIn_le hc0).trans hci), (min_le_left _ _).trans hhi⟩⟩

/-! ### Values on the rectangles and on the axes -/

/-- **`M* = M` on every rectangle**: if `s ≤ S₁ i`, `t ≤ S₂ i` (and `m(0, ·) = 0`), then `patchLog = m`. -/
theorem patchLog_eq_of_inStair (hS₁ : ∀ i, 0 ≤ S₁ i) {m : ℝ → ℝ → ℝ} (hm0 : ∀ y, m 0 y = 0) {s t : ℝ}
    (hs : 0 ≤ s) {i : ι} (hsi : s ≤ S₁ i) (hti : t ≤ S₂ i) : patchLog S₁ S₂ m s t = m s t := by
  set C := stairCols S₁ with hCdef
  have hC : ∀ c ∈ C, 0 ≤ c := fun c hc => nonneg_of_mem_stairCols hS₁ hc
  have key : ∀ c ∈ C, m (min c s) (min (stairH S₁ S₂ c) t) - m (min (prevIn C c) s) (min (stairH S₁ S₂ c) t) =
      m (min c s) t - m (min (prevIn C c) s) t := by
    intro c hc
    by_cases hp : prevIn C c < s
    · have hci : c ≤ S₁ i := by
        by_contra h
        exact absurd ((le_prevIn (mem_stairCols i) (not_le.1 h)).trans_lt hp) (not_lt.2 hsi)
      rw [min_eq_right (hti.trans (le_stairH hci))]
    · have h1 : min (prevIn C c) s = s := min_eq_right (not_lt.1 hp)
      have h2 : min c s = s := min_eq_right ((not_lt.1 hp).trans (prevIn_le (hC c hc)))
      rw [h1, h2, sub_self, sub_self]
  rw [patchLog, ← hCdef, sum_congr rfl key, sum_sub_prevIn C hC fun x => m (min x s) t,
    min_eq_right (hsi.trans (le_maxIn (mem_stairCols i))), min_eq_left hs, hm0, sub_zero]

/-- **`M* = 1` on the axis `s = 0`.** -/
theorem patchLog_zero_left (hS₁ : ∀ i, 0 ≤ S₁ i) (m : ℝ → ℝ → ℝ) (t : ℝ) : patchLog S₁ S₂ m 0 t = 0 := by
  refine sum_eq_zero fun c hc => ?_
  rw [min_eq_right (nonneg_of_mem_stairCols hS₁ hc), min_eq_right (prevIn_nonneg _ _), sub_self]

/-- **`M* = 1` on the axis `t = 0`** (given `m(·, 0) = 0`). -/
theorem patchLog_zero_right (m : ℝ → ℝ → ℝ) (hm0 : ∀ x, m x 0 = 0) (s : ℝ) : patchLog S₁ S₂ m s 0 = 0 := by
  refine sum_eq_zero fun c _ => ?_
  rw [min_eq_right (stairH_nonneg c), hm0, hm0, sub_self]

/-! ### Bounds and continuity -/

/-- **Bounds**: if `|m| ≤ K` on the staircase, then `|patchLog| ≤ 2 |ι| K`. -/
theorem abs_patchLog_le (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i) {m : ℝ → ℝ → ℝ} {K : ℝ}
    (hK : ∀ x y, 0 ≤ x → 0 ≤ y → InStair S₁ S₂ x y → |m x y| ≤ K) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |patchLog S₁ S₂ m s t| ≤ 2 * Fintype.card ι * K := by
  set C := stairCols S₁ with hCdef
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
  · have hC : C = ∅ := by rw [hCdef, stairCols, univ_eq_empty, Finset.image_empty]
    rw [patchLog, ← hCdef, hC, sum_empty, abs_zero, Fintype.card_eq_zero, Nat.cast_zero, mul_zero, zero_mul]
  · have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 0 le_rfl le_rfl ⟨i, hS₁ i, hS₂ i⟩)
    have hterm : ∀ c ∈ C, |m (min c s) (min (stairH S₁ S₂ c) t) - m (min (prevIn C c) s) (min (stairH S₁ S₂ c) t)|
        ≤ 2 * K := by
      intro c hc
      have hc0 := nonneg_of_mem_stairCols hS₁ hc
      obtain ⟨h1, h2⟩ := inStair_args (S₁ := S₁) hS₂ hc hc0 s t
      have e1 := hK _ _ (le_min hc0 hs) (le_min (stairH_nonneg c) ht) h1
      have e2 := hK _ _ (le_min (prevIn_nonneg _ _) hs) (le_min (stairH_nonneg c) ht) h2
      exact (abs_sub _ _).trans (by linarith)
    have hcard : (C.card : ℝ) ≤ Fintype.card ι := by
      rw [hCdef, stairCols]
      exact_mod_cast (card_image_le).trans (card_univ (α := ι)).le
    calc |patchLog S₁ S₂ m s t| ≤ ∑ c ∈ C, |m (min c s) (min (stairH S₁ S₂ c) t) -
          m (min (prevIn C c) s) (min (stairH S₁ S₂ c) t)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _c ∈ C, 2 * K := sum_le_sum hterm
      _ = C.card * (2 * K) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card ι * (2 * K) := mul_le_mul_of_nonneg_right hcard (by linarith)
      _ = 2 * Fintype.card ι * K := by ring

/-- **Continuity**: if `m` is continuous on the staircase (in the closed quadrant), `patchLog` is continuous on the
closed quadrant. -/
theorem continuousOn_patchLog (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i) {m : ℝ → ℝ → ℝ}
    (hm : ContinuousOn (fun p : ℝ × ℝ => m p.1 p.2) {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ InStair S₁ S₂ p.1 p.2}) :
    ContinuousOn (fun p : ℝ × ℝ => patchLog S₁ S₂ m p.1 p.2) {p | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
  unfold patchLog
  refine continuousOn_finsetSum _ fun c hc => ?_
  have hc0 := nonneg_of_mem_stairCols hS₁ hc
  have h1 : ContinuousOn ((fun p : ℝ × ℝ => m p.1 p.2) ∘ fun p : ℝ × ℝ => (min c p.1, min (stairH S₁ S₂ c) p.2))
      {p | 0 ≤ p.1 ∧ 0 ≤ p.2} :=
    hm.comp ((continuous_const.min continuous_fst).prodMk (continuous_const.min continuous_snd)).continuousOn
      fun p hp => ⟨le_min hc0 hp.1, le_min (stairH_nonneg c) hp.2, (inStair_args hS₂ hc hc0 p.1 p.2).1⟩
  have h2 : ContinuousOn ((fun p : ℝ × ℝ => m p.1 p.2) ∘
      fun p : ℝ × ℝ => (min (prevIn (stairCols S₁) c) p.1, min (stairH S₁ S₂ c) p.2)) {p | 0 ≤ p.1 ∧ 0 ≤ p.2} :=
    hm.comp ((continuous_const.min continuous_fst).prodMk (continuous_const.min continuous_snd)).continuousOn
      fun p hp => ⟨le_min (prevIn_nonneg _ _) hp.1, le_min (stairH_nonneg c) hp.2,
        (inStair_args hS₂ hc hc0 p.1 p.2).2⟩
  exact h1.sub h2

/-! ### The adapted (column) structure, (D12) -/

/-- **One column at a time.** For `s ∈ [prev c, c]` only the column `c` moves:
`log M*(s, t) = log M*(prev c, t) + m(s, h c ∧ t) − m(prev c, h c ∧ t)`. This is the deterministic content of the
adapted recursion (D12): on `[R_{k−1}, R_k] = [prev c, c]` the ratio of `M*` to its value at `R_{k−1}` is
`M(s, I_k)/M(R_{k−1}, I_k)` with `I_k = h c ∧ t`. -/
theorem patchLog_column (hS₁ : ∀ i, 0 ≤ S₁ i) (m : ℝ → ℝ → ℝ) {c : ℝ} (hc : c ∈ stairCols S₁) {s : ℝ}
    (hs1 : prevIn (stairCols S₁) c ≤ s) (hs2 : s ≤ c) (t : ℝ) :
    patchLog S₁ S₂ m s t = patchLog S₁ S₂ m (prevIn (stairCols S₁) c) t +
      (m s (min (stairH S₁ S₂ c) t) - m (prevIn (stairCols S₁) c) (min (stairH S₁ S₂ c) t)) := by
  set C := stairCols S₁ with hCdef
  set x := prevIn C c with hx
  have hC : ∀ c ∈ C, 0 ≤ c := fun c hc => nonneg_of_mem_stairCols hS₁ hc
  unfold patchLog
  rw [← hCdef, ← add_sum_erase C _ hc, ← add_sum_erase C _ hc]
  have hrest : ∀ c' ∈ C.erase c,
      m (min c' s) (min (stairH S₁ S₂ c') t) - m (min (prevIn C c') s) (min (stairH S₁ S₂ c') t) =
      m (min c' x) (min (stairH S₁ S₂ c') t) - m (min (prevIn C c') x) (min (stairH S₁ S₂ c') t) := by
    intro c' hc'
    obtain ⟨hne, hc'C⟩ := mem_erase.1 hc'
    have hc'0 := hC c' hc'C
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : c' ≤ x := le_prevIn hc'C hlt
      have h2 : prevIn C c' ≤ x := (prevIn_le hc'0).trans h1
      rw [min_eq_left (h1.trans hs1), min_eq_left h1, min_eq_left (h2.trans hs1), min_eq_left h2]
    · have h1 : c ≤ prevIn C c' := le_prevIn hc hgt
      have h2 : s ≤ prevIn C c' := hs2.trans h1
      have h3 : x ≤ prevIn C c' := hs1.trans h2
      rw [min_eq_right (h2.trans (prevIn_le hc'0)), min_eq_right h2, min_eq_right (h3.trans (prevIn_le hc'0)),
        min_eq_right h3, sub_self, sub_self]
  rw [sum_congr rfl hrest, min_eq_right hs2, min_eq_left hs1, min_eq_right (hs1.trans hs2), min_self]
  ring

/-- **Constant after the last column**: for `s ≥ max C`, `log M*(s, t) = log M*(max C, t)`. -/
theorem patchLog_of_maxIn_le (hS₁ : ∀ i, 0 ≤ S₁ i) (m : ℝ → ℝ → ℝ) {s : ℝ} (hs : maxIn (stairCols S₁) ≤ s)
    (t : ℝ) : patchLog S₁ S₂ m s t = patchLog S₁ S₂ m (maxIn (stairCols S₁)) t := by
  refine sum_congr rfl fun c hc => ?_
  have hcM := le_maxIn hc
  have hpc := prevIn_le (C := stairCols S₁) (nonneg_of_mem_stairCols hS₁ hc)
  rw [min_eq_left (hcM.trans hs), min_eq_left hcM, min_eq_left ((hpc.trans hcM).trans hs),
    min_eq_left (hpc.trans hcM)]

/-- **The next column end is known at the previous one**: every rectangle not yet exited at `prev c` reaches over the
whole column, `prev c < S₁ i → c ≤ S₁ i`. -/
theorem le_of_prevIn_lt {c : ℝ} {i : ι} (hi : prevIn (stairCols S₁) c < S₁ i) :
    c ≤ S₁ i := by
  by_contra h
  exact absurd (le_prevIn (mem_stairCols i) (not_le.1 h)) (not_le.2 hi)

/-- **The column height is known at the previous column end**: for `c > 0`, `h c = max{S₂ i : prev c < S₁ i}`
(or `0`): the maximum over the rectangles not yet exited at `prev c`. -/
theorem stairH_eq_of_prevIn_lt {c : ℝ} (hc0 : 0 < c) :
    stairH S₁ S₂ c = (insert 0 ((univ.filter fun i => prevIn (stairCols S₁) c < S₁ i).image S₂)).max'
      (insert_nonempty _ _) := by
  unfold stairH
  congr 2
  exact congrArg (Finset.image S₂)
    (filter_congr fun i _ => ⟨fun h => (prevIn_lt hc0).trans_le h, fun h => le_of_prevIn_lt h⟩)

/-! ### Reflection: the construction is symmetric in the two coordinates -/

theorem prevIn_filter_le {C : Finset ℝ} {h d : ℝ} (hd : d ≤ h) :
    prevIn (C.filter (· ≤ h)) d = prevIn C d := by
  unfold prevIn
  congr 2
  ext y
  simp only [mem_filter]
  exact ⟨fun hy => ⟨hy.1.1, hy.2⟩, fun hy => ⟨⟨hy.1, hy.2.le.trans hd⟩, hy.2⟩⟩

theorem maxIn_filter_le {C : Finset ℝ} {h : ℝ} (h0 : 0 ≤ h) (hmem : h = 0 ∨ h ∈ C) :
    maxIn (C.filter (· ≤ h)) = h := by
  refine le_antisymm (max'_le _ _ _ fun y hy => ?_) ?_
  · rcases mem_insert.1 hy with rfl | hy
    · exact h0
    · exact (mem_filter.1 hy).2
  · rcases hmem with rfl | hmem
    · exact maxIn_nonneg _
    · exact le_maxIn (mem_filter.2 ⟨hmem, le_rfl⟩)

theorem stairH_eq_zero_or_mem (c : ℝ) : stairH S₁ S₂ c = 0 ∨ stairH S₁ S₂ c ∈ stairCols S₂ := by
  have h : stairH S₁ S₂ c ∈ insert 0 ((univ.filter fun i => c ≤ S₁ i).image S₂) := max'_mem _ _
  rcases mem_insert.1 h with h | h
  · exact Or.inl h
  · obtain ⟨i, -, he⟩ := mem_image.1 h
    exact Or.inr (he ▸ mem_stairCols i)

theorem le_stairH_iff (hS₂ : ∀ i, 0 ≤ S₂ i) {c : ℝ} (hc : c ∈ stairCols S₁) (d : ℝ) :
    d ≤ stairH S₁ S₂ c ↔ InStair S₁ S₂ c d := by
  constructor
  · intro hd
    obtain ⟨i, hci, hhi⟩ := exists_stairH_le (S₁ := S₁) hS₂ hc
    exact ⟨i, hci, hd.trans hhi⟩
  · rintro ⟨i, hci, hdi⟩
    exact hdi.trans (le_stairH hci)

/-- The rectangle increment of `m` over the grid cell `[prev c, c] × [prev d, d]`, cut at `(s, t)`. -/
def cellInc (C₁ C₂ : Finset ℝ) (m : ℝ → ℝ → ℝ) (s t c d : ℝ) : ℝ :=
  m (min c s) (min d t) - m (min (prevIn C₁ c) s) (min d t) - m (min c s) (min (prevIn C₂ d) t) +
    m (min (prevIn C₁ c) s) (min (prevIn C₂ d) t)

open Classical in
/-- **The double-sum form**: `log M*(s, t)` is the sum of the rectangle increments of `m` over the grid cells that lie
in the staircase. -/
theorem patchLog_eq_sum_cells (hS₂ : ∀ i, 0 ≤ S₂ i) {m : ℝ → ℝ → ℝ}
    (hm0 : ∀ x, m x 0 = 0) (s : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    patchLog S₁ S₂ m s t = ∑ c ∈ stairCols S₁, ∑ d ∈ stairCols S₂,
      if InStair S₁ S₂ c d then cellInc (stairCols S₁) (stairCols S₂) m s t c d else 0 := by
  refine sum_congr rfl fun c hc => ?_
  rw [← sum_filter]
  set D := (stairCols S₂).filter fun d => InStair S₁ S₂ c d with hD
  have hD' : D = (stairCols S₂).filter (· ≤ stairH S₁ S₂ c) :=
    filter_congr fun d _ => (le_stairH_iff hS₂ hc d).symm
  have hD0 : ∀ d ∈ D, 0 ≤ d := fun d hd => nonneg_of_mem_stairCols hS₂ (mem_filter.1 hd).1
  set G : ℝ → ℝ := fun y => m (min c s) (min y t) - m (min (prevIn (stairCols S₁) c) s) (min y t) with hG
  have hsum : ∑ d ∈ D, cellInc (stairCols S₁) (stairCols S₂) m s t c d = ∑ d ∈ D, (G d - G (prevIn D d)) := by
    refine sum_congr rfl fun d hd => ?_
    have hdh : d ≤ stairH S₁ S₂ c := by rw [hD'] at hd; exact (mem_filter.1 hd).2
    rw [hD', prevIn_filter_le hdh]
    simp only [cellInc, hG]
    ring
  rw [hsum, sum_sub_prevIn D hD0 G, hD', maxIn_filter_le (stairH_nonneg c) (stairH_eq_zero_or_mem c)]
  simp only [hG, min_eq_left ht, hm0, sub_zero]

open Classical in
/-- **Reflection** (§A.1.4: "Reflection of the construction proves the corresponding martingale in the other
coordinate"): exchanging the roles of the two coordinates gives the same patched function. -/
theorem patchLog_symm (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i) {m : ℝ → ℝ → ℝ} (hm0 : ∀ y, m 0 y = 0)
    (hm0' : ∀ x, m x 0 = 0) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    patchLog S₁ S₂ m s t = patchLog S₂ S₁ (fun y x => m x y) t s := by
  rw [patchLog_eq_sum_cells hS₂ hm0' s ht, patchLog_eq_sum_cells hS₁ (m := fun y x => m x y) hm0 t hs,
    sum_comm]
  refine sum_congr rfl fun d _ => sum_congr rfl fun c _ => ?_
  have hiff : InStair S₁ S₂ c d ↔ InStair S₂ S₁ d c :=
    ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩
  simp only [hiff, cellInc]
  split_ifs <;> ring

/-! ### The multiplicative form `M*` -/

/-- **The patched density `M*`, (D11)**: `M* = exp (patchLog (log M))`. -/
def patch (S₁ S₂ : ι → ℝ) (M : ℝ → ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.exp (patchLog S₁ S₂ (fun x y => Real.log (M x y)) s t)

variable {M : ℝ → ℝ → ℝ}

theorem patch_pos (s t : ℝ) : 0 < patch S₁ S₂ M s t := Real.exp_pos _

/-- **`M*` as a product over the columns**, `∏_c M(c ∧ s, h c ∧ t)/M(prev c ∧ s, h c ∧ t)`, when `M > 0` on the
staircase. On the cell `a_{i−1} ≤ s ≤ a_i`, `b_{j+1} ≤ t ≤ b_j` of the non-dominated corners this is the display
(D11) (see the module docstring). -/
theorem patch_eq_prod (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i)
    (hM : ∀ x y, 0 ≤ x → 0 ≤ y → InStair S₁ S₂ x y → 0 < M x y) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    patch S₁ S₂ M s t = ∏ c ∈ stairCols S₁,
      M (min c s) (min (stairH S₁ S₂ c) t) / M (min (prevIn (stairCols S₁) c) s) (min (stairH S₁ S₂ c) t) := by
  unfold patch patchLog
  rw [Real.exp_sum]
  refine prod_congr rfl fun c hc => ?_
  have hc0 := nonneg_of_mem_stairCols hS₁ hc
  obtain ⟨h1, h2⟩ := inStair_args (S₁ := S₁) hS₂ hc hc0 s t
  rw [Real.exp_sub, Real.exp_log (hM _ _ (le_min hc0 hs) (le_min (stairH_nonneg c) ht) h1),
    Real.exp_log (hM _ _ (le_min (prevIn_nonneg _ _) hs) (le_min (stairH_nonneg c) ht) h2)]

/-- **`M* = M` on every rectangle** (axis values of `M` equal to one). -/
theorem patch_eq_of_inStair (hS₁ : ∀ i, 0 ≤ S₁ i) (hM1 : ∀ y, M 0 y = 1) {s t : ℝ} (hs : 0 ≤ s) {i : ι}
    (hsi : s ≤ S₁ i) (hti : t ≤ S₂ i) (hpos : 0 < M s t) : patch S₁ S₂ M s t = M s t := by
  unfold patch
  rw [patchLog_eq_of_inStair hS₁ (fun y => by simp only [hM1, Real.log_one]) hs hsi hti, Real.exp_log hpos]

/-- **`M* = 1` on the axis `s = 0`.** -/
theorem patch_zero_left (hS₁ : ∀ i, 0 ≤ S₁ i) (M : ℝ → ℝ → ℝ) (t : ℝ) : patch S₁ S₂ M 0 t = 1 := by
  unfold patch
  rw [patchLog_zero_left hS₁, Real.exp_zero]

/-- **`M* = 1` on the axis `t = 0`** (axis values of `M` equal to one). -/
theorem patch_zero_right (hM1 : ∀ x, M x 0 = 1) (s : ℝ) : patch S₁ S₂ M s 0 = 1 := by
  unfold patch
  rw [patchLog_zero_right _ (fun x => by simp only [hM1, Real.log_one]), Real.exp_zero]

/-- **Deterministic positive bounds** (from (D9)): if `c ≤ M ≤ C` on the staircase (`0 < c`), then
`exp(−2|ι|K) ≤ M* ≤ exp(2|ι|K)`, `K = max |log c| |log C|`. -/
theorem patch_mem_Icc (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i) {c C : ℝ} (hc : 0 < c)
    (hM : ∀ x y, 0 ≤ x → 0 ≤ y → InStair S₁ S₂ x y → c ≤ M x y ∧ M x y ≤ C) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) :
    patch S₁ S₂ M s t ∈ Icc (Real.exp (-(2 * Fintype.card ι * max |Real.log c| |Real.log C|)))
      (Real.exp (2 * Fintype.card ι * max |Real.log c| |Real.log C|)) := by
  have hK : ∀ x y, 0 ≤ x → 0 ≤ y → InStair S₁ S₂ x y →
      |(fun x y => Real.log (M x y)) x y| ≤ max |Real.log c| |Real.log C| := by
    intro x y hx hy hxy
    obtain ⟨h1, h2⟩ := hM x y hx hy hxy
    have l1 := Real.log_le_log hc h1
    have l2 := Real.log_le_log (hc.trans_le h1) h2
    rw [abs_le]
    exact ⟨(neg_le_neg (le_max_left _ _)).trans ((neg_abs_le _).trans l1),
      l2.trans ((le_abs_self _).trans (le_max_right _ _))⟩
  have h := abs_patchLog_le hS₁ hS₂ hK hs ht
  rw [abs_le] at h
  exact ⟨Real.exp_le_exp.2 h.1, Real.exp_le_exp.2 h.2⟩

/-- **Continuity of `M*`** from continuity and positivity of `M` on the staircase. -/
theorem continuousOn_patch (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i)
    (hM : ContinuousOn (fun p : ℝ × ℝ => M p.1 p.2) {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ InStair S₁ S₂ p.1 p.2})
    (hpos : ∀ p ∈ {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ InStair S₁ S₂ p.1 p.2}, M p.1 p.2 ≠ 0) :
    ContinuousOn (fun p : ℝ × ℝ => patch S₁ S₂ M p.1 p.2) {p | 0 ≤ p.1 ∧ 0 ≤ p.2} :=
  Real.continuous_exp.comp_continuousOn (continuousOn_patchLog hS₁ hS₂ (hM.log hpos))

/-- **One column at a time, multiplicatively**: for `s ∈ [prev c, c]`,
`M*(s, t) = M*(prev c, t) · M(s, h c ∧ t)/M(prev c, h c ∧ t)`. -/
theorem patch_column (hS₁ : ∀ i, 0 ≤ S₁ i) {c : ℝ} (hc : c ∈ stairCols S₁) {s : ℝ}
    (hs1 : prevIn (stairCols S₁) c ≤ s) (hs2 : s ≤ c) (t : ℝ) (h1 : 0 < M s (min (stairH S₁ S₂ c) t))
    (h2 : 0 < M (prevIn (stairCols S₁) c) (min (stairH S₁ S₂ c) t)) :
    patch S₁ S₂ M s t = patch S₁ S₂ M (prevIn (stairCols S₁) c) t *
      (M s (min (stairH S₁ S₂ c) t) / M (prevIn (stairCols S₁) c) (min (stairH S₁ S₂ c) t)) := by
  unfold patch
  rw [patchLog_column hS₁ _ hc hs1 hs2 t, Real.exp_add, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]

/-- **Reflection, multiplicatively.** -/
theorem patch_symm (hS₁ : ∀ i, 0 ≤ S₁ i) (hS₂ : ∀ i, 0 ≤ S₂ i) (hM1 : ∀ y, M 0 y = 1) (hM1' : ∀ x, M x 0 = 1)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : patch S₁ S₂ M s t = patch S₂ S₁ (fun y x => M x y) t s := by
  unfold patch
  rw [patchLog_symm hS₁ hS₂ (fun y => by simp only [hM1, Real.log_one])
    (fun x => by simp only [hM1', Real.log_one]) hs ht]

end InteractingSLE.ZhanGT4
