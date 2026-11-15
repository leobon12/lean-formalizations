/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualD12

/-!
# Zhan's A.1.4, (D12): the columns in increasing order

Packet PROVE-ZHAN-GT4-A13. Source: Astra, *Follow-up proofs*, §A.1.4 (`ig1_followup_proofs.txt` L385–L407, R38): the
recursion (D12) visits the columns `[R_{k−1}, R_k]` of the staircase in increasing order; "after at most `n` such
intervals it is constant".

The closed form of (D11) (`patchLog`, `patch_mul_marginal`) is a product over the finite set `C` of column ends; the
martingale argument (`martingale_concatProc`) runs over the column ends **in increasing order**, `τ₀ = 0`,
`τ_{k+1} = nextIn C τ_k` (the least column end above `τ_k`, or `τ_k` if there is none). Here:

* `prod_colSeq_eq`: for `f` with `f y y = 1`, `∏_{k<n} f(τ_{k+1}, τ_k) = ∏_{c ∈ C} f(c, prevIn C c)` once `n ≥ |C|`;
* `concatProc_eq_prod`: the concatenated process is the product of its column ratios.
-/

set_option autoImplicit false

noncomputable section

open Set Finset Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-! ### The column ends in increasing order -/

/-- The least element of `C` above `x`, or `x` if there is none. -/
def nextIn (C : Finset ℝ) (x : ℝ) : ℝ :=
  if h : (C.filter (x < ·)).Nonempty then (C.filter (x < ·)).min' h else x

/-- The column ends above `x` in increasing order: `colSeq C x k = (nextIn C)^[k] x`. -/
def colSeq (C : Finset ℝ) (x : ℝ) (k : ℕ) : ℝ := (nextIn C)^[k] x

/-- The largest element of `insert x (D below d)`. -/
def prevAbove (x : ℝ) (D : Finset ℝ) (d : ℝ) : ℝ := (insert x (D.filter (· < d))).max' (insert_nonempty _ _)

theorem le_nextIn (C : Finset ℝ) (x : ℝ) : x ≤ nextIn C x := by
  unfold nextIn
  split_ifs with h
  · exact ((Finset.mem_filter.1 ((C.filter (x < ·)).min'_mem h)).2).le
  · exact le_rfl

theorem le_colSeq (C : Finset ℝ) (x : ℝ) (k : ℕ) : x ≤ colSeq C x k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    unfold colSeq at ih ⊢
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_nextIn C _)

/-- Above the least element `c₁`, `nextIn` only sees the elements above `c₁`. -/
theorem nextIn_filter_of_le {C : Finset ℝ} {c₁ y : ℝ} (hy : c₁ ≤ y) :
    nextIn (C.filter (c₁ < ·)) y = nextIn C y := by
  have e : (C.filter (c₁ < ·)).filter (y < ·) = C.filter (y < ·) := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hy.trans_lt h.2⟩, h.2⟩⟩
  unfold nextIn
  simp only [e]

theorem colSeq_filter {C : Finset ℝ} {c₁ x : ℝ} (hx : c₁ ≤ x) (k : ℕ) :
    colSeq (C.filter (c₁ < ·)) x k = colSeq C x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold colSeq at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact nextIn_filter_of_le (hx.trans (le_colSeq C x k))

/-- **The ordered enumeration of the columns.** For a finite `D` above `x` and `f` with `f y y = 1`,
`∏_{k<n} f(e_{k+1}, e_k) = ∏_{d ∈ D} f(d, prevAbove x D d)` for `n ≥ |D|`, `e = colSeq D x`. -/
theorem prod_colSeq_eq_aux (f : ℝ → ℝ → ℝ) (hf : ∀ y, f y y = 1) :
    ∀ (n : ℕ) (D : Finset ℝ) (x : ℝ), (∀ d ∈ D, x < d) → D.card ≤ n →
      ∏ k ∈ Finset.range n, f (colSeq D x (k + 1)) (colSeq D x k) = ∏ d ∈ D, f d (prevAbove x D d) := by
  intro n
  induction n with
  | zero =>
    intro D x _ hcard
    have hD : D = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    simp [hD]
  | succ m ih =>
    intro D x hxD hcard
    rcases D.eq_empty_or_nonempty with hD | hDne
    · -- no columns: every step stays at `x`
      subst hD
      have hst : ∀ k, colSeq (∅ : Finset ℝ) x k = x := fun k => by
        induction k with
        | zero => rfl
        | succ k ihk =>
          unfold colSeq at ihk ⊢
          rw [Function.iterate_succ_apply', ihk]
          simp [nextIn]
      simp [hst, hf]
    · set c₁ := D.min' hDne with hc₁
      have hc₁D : c₁ ∈ D := D.min'_mem hDne
      have hfilt : D.filter (x < ·) = D := Finset.filter_true_of_mem fun d hd => hxD d hd
      have hnext : nextIn D x = c₁ := by
        unfold nextIn
        simp only [hfilt, hDne, ↓reduceDIte]
        rfl
      set D' := D.filter (c₁ < ·) with hD'
      have hD'eq : D' = D.erase c₁ := by
        ext d
        simp only [hD', Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hd, hlt⟩; exact ⟨hlt.ne', hd⟩
        · rintro ⟨hne, hd⟩; exact ⟨hd, lt_of_le_of_ne (D.min'_le d hd) hne.symm⟩
      have hcardD' : D'.card ≤ m := by
        rw [hD'eq, Finset.card_erase_of_mem hc₁D]; omega
      have hxD' : ∀ d ∈ D', c₁ < d := fun d hd => (Finset.mem_filter.1 hd).2
      have hshift : ∀ k, colSeq D x (k + 1) = colSeq D' c₁ k := fun k => by
        rw [colSeq_filter le_rfl k]
        unfold colSeq
        rw [Function.iterate_succ_apply, hnext]
      rw [Finset.prod_range_succ']
      simp only [hshift]
      rw [ih D' c₁ hxD' hcardD', ← Finset.mul_prod_erase D (fun d => f d (prevAbove x D d)) hc₁D, ← hD'eq]
      have hprev₁ : prevAbove x D c₁ = x := by
        have : D.filter (· < c₁) = ∅ := Finset.filter_false_of_mem fun d hd => not_lt.2 (D.min'_le d hd)
        simp [prevAbove, this]
      have hcol0 : colSeq D' c₁ 0 = c₁ := rfl
      have hx0 : colSeq D x 0 = x := rfl
      rw [hcol0, hx0, hprev₁, mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun d hd => ?_
      congr 1
      -- `prevAbove x D d = prevAbove c₁ D' d` for `d > c₁`
      have hd₁ : c₁ < d := hxD' d hd
      have hset : insert x (D.filter (· < d)) = insert x (insert c₁ (D'.filter (· < d))) := by
        congr 1
        ext e
        simp only [Finset.mem_filter, Finset.mem_insert, hD']
        constructor
        · rintro ⟨he, hed⟩
          by_cases hec : e = c₁
          · exact Or.inl hec
          · exact Or.inr ⟨⟨he, lt_of_le_of_ne (D.min'_le e he) (Ne.symm hec)⟩, hed⟩
        · rintro (rfl | ⟨⟨he, -⟩, hed⟩)
          · exact ⟨hc₁D, hd₁⟩
          · exact ⟨he, hed⟩
      unfold prevAbove
      simp only [hset]
      refine le_antisymm (Finset.max'_le _ _ _ fun e he => Finset.le_max' _ _ (Finset.mem_insert_of_mem he))
        (Finset.max'_le _ _ _ fun e he => ?_)
      rcases Finset.mem_insert.1 he with rfl | he'
      · exact (hxD c₁ hc₁D).le.trans (Finset.le_max' _ _ (Finset.mem_insert_self _ _))
      · exact Finset.le_max' _ _ he'

/-- **The columns in increasing order give the closed form of (D11).** For a finite set `C` of nonnegative column
ends, `f` with `f y y = 1` and `n ≥ |C|`: `∏_{k<n} f(τ_{k+1}, τ_k) = ∏_{c ∈ C} f(c, prevIn C c)`, `τ = colSeq C 0`. -/
theorem prod_colSeq_eq (f : ℝ → ℝ → ℝ) (hf : ∀ y, f y y = 1) {C : Finset ℝ} (hC : ∀ c ∈ C, 0 ≤ c) {n : ℕ}
    (hn : C.card ≤ n) :
    ∏ k ∈ Finset.range n, f (colSeq C 0 (k + 1)) (colSeq C 0 k) = ∏ c ∈ C, f c (prevIn C c) := by
  set D := C.filter (0 < ·) with hD
  have hDC : ∀ k, colSeq D 0 k = colSeq C 0 k := colSeq_filter le_rfl
  have h := prod_colSeq_eq_aux f hf n D 0 (fun d hd => (Finset.mem_filter.1 hd).2)
    ((Finset.card_filter_le _ _).trans hn)
  simp only [hDC] at h
  rw [h]
  -- the possible column end `0` contributes `f 0 0 = 1`; above `0`, `prevIn = prevAbove 0`
  have hsplit := Finset.prod_filter_mul_prod_filter_not C (fun c => 0 < c) (fun c => f c (prevIn C c))
  rw [← hsplit]
  have hzero : ∏ c ∈ C.filter (fun c => ¬ 0 < c), f c (prevIn C c) = 1 := by
    refine Finset.prod_eq_one fun c hc => ?_
    obtain ⟨hcC, hc0⟩ := Finset.mem_filter.1 hc
    have hc : c = 0 := le_antisymm (not_lt.1 hc0) (hC c hcC)
    subst hc
    rw [show prevIn C 0 = 0 from le_antisymm (Finset.max'_le _ _ _ fun e he => ?_) (prevIn_nonneg C 0), hf]
    rcases Finset.mem_insert.1 he with rfl | he'
    · exact le_rfl
    · exact absurd (Finset.mem_filter.1 he').2 (not_lt.2 (hC e (Finset.mem_filter.1 he').1))
  rw [hzero, mul_one]
  refine Finset.prod_congr rfl fun c hc => ?_
  congr 1
  have hc0 : 0 < c := (Finset.mem_filter.1 hc).2
  unfold prevAbove prevIn
  congr 1
  ext e
  simp only [Finset.mem_insert, Finset.mem_filter, hD]
  constructor
  · rintro (rfl | ⟨⟨he, -⟩, hec⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨he, hec⟩
  · rintro (rfl | ⟨he, hec⟩)
    · exact Or.inl rfl
    · by_cases he0 : 0 < e
      · exact Or.inr ⟨⟨he, he0⟩, hec⟩
      · exact Or.inl (le_antisymm (not_lt.1 he0) (hC e he))

/-! ### The concatenation is the product of its column ratios -/

section Concat

variable {Ω : Type*}

/-- Stopping at `ρ` after stopping at a later `ρ'` is stopping at `ρ`. -/
theorem stoppedProcess_untopA_min {X : ℝ≥0 → Ω → ℝ} {ρ ρ' : Ω → WithTop ℝ≥0} {ω : Ω} (h : ρ ω ≤ ρ' ω)
    (s : ℝ≥0) : stoppedProcess X ρ (min (s : WithTop ℝ≥0) (ρ' ω)).untopA ω = stoppedProcess X ρ s ω := by
  by_cases hρ' : ρ' ω = ⊤
  · simp only [hρ', le_top, min_eq_left, WithTop.untopA, WithTop.untopD_coe]
  · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hρ'
    have e : (min (s : WithTop ℝ≥0) (ρ' ω)).untopA = min s a := by
      rw [← ha, ← WithTop.coe_min]; simp only [WithTop.untopA, WithTop.untopD_coe]
    simp only [stoppedProcess, e]
    congr 2
    rw [WithTop.coe_min, ha, min_assoc, min_eq_right h]

/-- **`concatProc` is the product of its column ratios** (for increasing `τ`). -/
theorem concatProc_eq_prod {ι : Type*} (Y : ι → ℝ≥0 → Ω → ℝ) {τ : ℕ → Ω → WithTop ℝ≥0}
    (hmono : ∀ k, τ k ≤ τ (k + 1)) (j : ℕ → Ω → ι) (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    concatProc Y τ j n s ω = ∏ k ∈ Finset.range n,
      (stoppedProcess (Y (j k ω)) (τ (k + 1)) s ω / stoppedProcess (Y (j k ω)) (τ k) s ω) := by
  have hmono' : ∀ a b, a ≤ b → τ a ≤ τ b := fun a b hab => by
    induction hab with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hmono _)
  induction n generalizing s with
  | zero => simp [concatProc]
  | succ n ih =>
    rw [Finset.prod_range_succ]
    show stoppedProcess (concatProc Y τ j n) (τ n) s ω * _ = _
    congr 1
    show concatProc Y τ j n (min (s : WithTop ℝ≥0) (τ n ω)).untopA ω = _
    rw [ih]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk' : k < n := Finset.mem_range.1 hk
    rw [stoppedProcess_untopA_min (hmono' (k + 1) n hk' ω), stoppedProcess_untopA_min (hmono' k n hk'.le ω)]

end Concat

end InteractingSLE.ZhanGT4
