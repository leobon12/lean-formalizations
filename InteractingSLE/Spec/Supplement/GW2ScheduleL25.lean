/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import InteractingSLE.GFF.Pushforward
import InteractingSLE.Frozen.Spec.Chart_tipSet

/-!
# Lemma 2.5: a Loewner trace spends zero Lebesgue time on the real line

Packet PROVE-T14-TIP3. Specification, Lemma 2.5 (`source/spec/p001-048.md`, anchors `lem-2.5`, `lem-2.5-proof`, p. 38):

> Suppose that `η` is a continuous (non-random) curve on `ℍ̄` from `0` to `∞` with a continuous Loewner driving
> function `W_t`. Then the set `{t : η(t) ∈ ℝ}` has Lebesgue measure zero.

It is the pathwise input of Lemma GB9a (p. 527: "Lemma 2.5 applied to the whole original-capacity concatenation"),
of GB9's countable interior stops (p. 527: "Interior tip times are therefore open and dense"), of CS3 (p. 593) and of
Lemma GW2 (p. 623: "Boundary time has zero occupation").

**Proof (the source's, on a finite grid instead of the components of `η⁻¹(S_δ)`).** Fix `T₁ < T` and `δ > 0`. Cut
`[0, T₁]` into `N` intervals `I_k` on which `η` oscillates by less than `δ`. If `η` meets `ℝ` on `I_k`, the compact
arc `C_k = η(I_k)` lies in the rectangle `[−a, a] × [0, δ]` and is attached to `ℝ`. With `A` the union of the earlier
bad arcs and `B = η([0, kh]) ⊇ A`, the capacity increment inequality (`hcapFill_union_union_sub_le`) gives
`2h = hcap(K_{(k+1)h}) − hcap(K_{kh}) ≤ hcap(A ∪ C_k) − hcap(A)`. Summing over the bad intervals,
`2h · #bad ≤ hcap(⋃ C_k) ≤ 2aδ + δ²` (thin rectangles, `hcapFill_le_of_subset_rect`). Hence the boundary time in
`[0, T₁]` is at most `aδ + δ²/2` for every `δ`, so it is null.

The trace never enters the open lower half-plane (`IsLoewnerTraceLT.im_nonneg`): on an interval where it did, the
hull would not grow, while `hcap(K_t) = 2t` is strictly increasing.

## Main results

* `IsLoewnerTraceLT.im_nonneg`: `0 ≤ Im η(t)` for `0 ≤ t < T`;
* `IsLoewnerTraceLT.volume_setOf_notMem_H`: **Lemma 2.5**, `|{t ∈ [0, T) : η(t) ∉ ℍ}| = 0`;
* `IsGeneratingTrace.volume_setOf_notMem_H`: the same for the frozen generating trace of a driver continuous before
  its lifetime `ζ`, `|{t ≥ 0 : t < ζ, η(t) ∉ ℍ}| = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Lemma25

/-! ### Capacity of the trace hulls -/

section Hull

variable {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ}

/-- The lower closed half-plane. -/
abbrev lowerHalf : Set ℂ := {z : ℂ | z.im ≤ 0}

theorem zero_mem_lowerHalf : (0 : ℂ) ∈ lowerHalf := show (0 : ℂ).im ≤ 0 by simp

/-- A preconnected set meeting the lower half-plane is preconnected together with it. -/
theorem isPreconnected_union_lowerHalf_of_mem {A : Set ℂ} (hA : IsPreconnected A) {z : ℂ} (hz : z ∈ A)
    (hzl : z.im ≤ 0) : IsPreconnected (A ∪ lowerHalf) :=
  hA.union z hz hzl isPreconnected_lowerHalf

theorem isPreconnected_image_Icc (hη : IsLoewnerTraceLT W T η) {s t : ℝ} (hs : 0 ≤ s) (htT : t < T) :
    IsPreconnected (η '' Icc s t) :=
  isPreconnected_Icc.image _ (hη.2.1.mono fun _ hu => ⟨hs.trans hu.1, lt_of_le_of_lt hu.2 htT⟩)

theorem isBounded_image_Icc (hη : IsLoewnerTraceLT W T η) {s t : ℝ} (hs : 0 ≤ s) (htT : t < T) :
    Bornology.IsBounded (η '' Icc s t) :=
  (hη.isCompact_image htT).isBounded.subset (image_mono (Icc_subset_Icc_left hs))

theorem isPreconnected_image_Icc_zero_union (hη : IsLoewnerTraceLT W T η) {t : ℝ} (ht : 0 ≤ t)
    (htT : t < T) : IsPreconnected (η '' Icc 0 t ∪ lowerHalf) :=
  isPreconnected_union_lowerHalf_of_mem (isPreconnected_image_Icc hη le_rfl htT)
    ⟨0, ⟨le_rfl, ht⟩, hη.1⟩ (by simp)

/-- **`hcap(fill(η[0, t])) = 2t`** before the horizon. -/
theorem hcapFill_image_Icc (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (htT : t < T) (hb : Bornology.IsBounded (η '' Icc 0 t))
    (hc : IsPreconnected (η '' Icc 0 t ∪ lowerHalf)) : hcapFill (η '' Icc 0 t) hb hc = 2 * t := by
  rw [← hcap_fwdHull hW hW0 ht]
  exact HPHull.hcap_congr (hη.2.2 t ht htT).symm

/-- The hull at time `t` only sees the trace in the closed upper half-plane. -/
theorem fillH_union_of_subset_lower {A B : Set ℂ} (hB : IsClosed B) (hBl : ∀ z ∈ B, z.im < 0) :
    fillH (A ∪ B) = fillH A := by
  refine fillH_congr ?_
  rw [closure_union, hB.closure_eq, union_inter_distrib_right]
  have : B ∩ H = ∅ := by
    refine eq_empty_of_forall_notMem fun z hz => ?_
    have h1 := hBl z hz.1
    have h2 : 0 < z.im := hz.2
    linarith
  rw [this, union_empty]

/-- **The trace never enters the open lower half-plane** before the horizon: on an interval where it did, the
hull would not grow, while `hcap(K_t) = 2t`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.im_nonneg (hη : IsLoewnerTraceLT W T η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (ht₀T : t₀ < T) : 0 ≤ (η t₀).im := by
  by_contra hneg
  push Not at hneg
  have hpos : 0 < t₀ := by
    rcases ht₀.lt_or_eq with h | h
    · exact h
    · rw [← h, hη.1] at hneg; simp at hneg
  -- continuity of `η` at the interior time `t₀`
  have hcont : ContinuousAt η t₀ :=
    (hη.2.1 t₀ ⟨ht₀, ht₀T⟩).continuousAt (Ico_mem_nhds hpos ht₀T)
  have hev : ∀ᶠ s in 𝓝 t₀, (η s).im < 0 :=
    (Complex.continuous_im.continuousAt.comp hcont).eventually (gt_mem_nhds hneg)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set s₁ := t₀ - min ε t₀ / 2 with hs₁
  have hm : 0 < min ε t₀ := lt_min hε hpos
  have hs₁0 : 0 ≤ s₁ := by
    have := min_le_right ε t₀
    rw [hs₁]; linarith
  have hs₁t : s₁ < t₀ := by rw [hs₁]; linarith
  have hlow : ∀ z ∈ η '' Icc s₁ t₀, z.im < 0 := by
    rintro _ ⟨s, hs, rfl⟩
    refine hball ?_
    rw [Real.dist_eq, abs_lt]
    have := min_le_left ε t₀
    constructor <;> linarith [hs.1, hs.2]
  have hclosed : IsClosed (η '' Icc s₁ t₀) := (hη.isCompact_image ht₀T |>.of_isClosed_subset
    ((isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun _ hu =>
      ⟨hs₁0.trans hu.1, lt_of_le_of_lt hu.2 ht₀T⟩)).isClosed) (image_mono (Icc_subset_Icc_left hs₁0))).isClosed
  have hsplit : η '' Icc 0 t₀ = η '' Icc 0 s₁ ∪ η '' Icc s₁ t₀ := by
    rw [← image_union, Icc_union_Icc_eq_Icc hs₁0 hs₁t.le]
  have heq : fwdHull W t₀ = fwdHull W s₁ := by
    rw [hη.2.2 t₀ ht₀ ht₀T, hη.2.2 s₁ hs₁0 (hs₁t.trans ht₀T), hsplit,
      fillH_union_of_subset_lower hclosed hlow]
  have h1 := hcap_fwdHull hW hW0 ht₀
  have h2 := hcap_fwdHull hW hW0 hs₁0
  have h3 : HPHull.hcap ⟨fwdHull W t₀, isHPHull_fwdHull hW ht₀⟩ =
      HPHull.hcap ⟨fwdHull W s₁, isHPHull_fwdHull hW hs₁0⟩ := HPHull.hcap_congr heq
  linarith

end Hull

/-! ### The grid estimate -/

section Grid

variable {W : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ}

/-- A point of `[0, N h]` lies in one of the `N` grid intervals `[kh, (k+1)h]`. -/
theorem exists_mem_grid {N : ℕ} (hN : 0 < N) {h t : ℝ} (hh : 0 ≤ h) (ht : t ∈ Icc 0 (N * h)) :
    ∃ k < N, t ∈ Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h) := by
  rcases hh.lt_or_eq with hh | hh
  · refine ⟨min ⌊t / h⌋₊ (N - 1), lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hN one_pos), ?_, ?_⟩
    · have : ((min ⌊t / h⌋₊ (N - 1) : ℕ) : ℝ) ≤ t / h :=
        (Nat.cast_le.2 (min_le_left _ _)).trans (Nat.floor_le (div_nonneg ht.1 hh.le))
      rwa [le_div_iff₀ hh] at this
    · rcases le_total ⌊t / h⌋₊ (N - 1) with hk | hk
      · rw [min_eq_left hk]
        have := Nat.lt_floor_add_one (t / h)
        rw [div_lt_iff₀ hh] at this
        exact this.le
      · rw [min_eq_right hk]
        have hN' : ((N - 1 : ℕ) : ℝ) + 1 = N := by
          rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hN.ne'), Nat.cast_one, sub_add_cancel]
        rw [hN']
        exact ht.2
  · subst hh
    refine ⟨0, hN, ?_, ?_⟩ <;> simp only [mul_zero, Nat.cast_zero] at ht ⊢
    · exact ht.1
    · exact ht.2

/-- A finite union of sets, each preconnected together with the lower half-plane, is preconnected together with it. -/
theorem isPreconnected_biUnion_union_lowerHalf {ι : Type*} (F : Finset ι) (C : ι → Set ℂ)
    (hC : ∀ k ∈ F, IsPreconnected (C k ∪ lowerHalf)) : IsPreconnected ((⋃ k ∈ F, C k) ∪ lowerHalf) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using isPreconnected_lowerHalf
  | insert a F haF ih =>
    rw [Finset.set_biUnion_insert]
    exact isPreconnected_union_lowerHalf (hC a (Finset.mem_insert_self a F))
      (ih fun k hk => hC k (Finset.mem_insert_of_mem hk))

theorem hcapFill_nonneg {A : Set ℂ} (hA : Bornology.IsBounded A) (hc : IsPreconnected (A ∪ lowerHalf)) :
    0 ≤ hcapFill A hA hc :=
  HPHull.hcap_nonneg _

/-- **The capacity count.** On a grid of mesh `h` covering `[0, N h] ⊂ [0, T)`, let `K` be a set of grid indices
whose arcs `C k = η([kh, (k+1)h])` are attached to the lower half-plane. Then `2h · #{k ∈ K, k < n}` is at most the
capacity of the union of those arcs. -/
theorem two_mul_card_le_hcapFill (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0) {N : ℕ}
    {h : ℝ} (hh : 0 ≤ h) (hNT : (N : ℝ) * h < T) (K : Finset ℕ)
    (hKc : ∀ k ∈ K, IsPreconnected (η '' Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h) ∪ lowerHalf))
    (hb : ∀ n : ℕ, Bornology.IsBounded (⋃ k ∈ K.filter (· < n), η '' Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h)))
    (n : ℕ) (hn : n ≤ N) :
    2 * h * (K.filter (· < n)).card ≤
      hcapFill (⋃ k ∈ K.filter (· < n), η '' Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h)) (hb n)
        (isPreconnected_biUnion_union_lowerHalf _ _ fun k hk => hKc k (Finset.mem_filter.1 hk).1) := by
  classical
  induction n with
  | zero =>
    have h0 : (K.filter (· < 0)).card = 0 :=
      Finset.card_eq_zero.2 (Finset.filter_false_of_mem fun k _ => Nat.not_lt_zero k)
    rw [h0, Nat.cast_zero, mul_zero]
    exact hcapFill_nonneg _ _
  | succ n ih =>
    have ih := ih (Nat.le_of_succ_le hn)
    set C : ℕ → Set ℂ := fun k => η '' Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h) with hCdef
    have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg n.cast_nonneg hh
    have hn1T : ((n : ℝ) + 1) * h < T := by
      refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right ?_ hh) hNT
      exact_mod_cast hn
    have hnT : (n : ℝ) * h < T := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith) hh) hn1T
    by_cases hnK : n ∈ K
    · have hfilt : K.filter (· < n + 1) = insert n (K.filter (· < n)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hk, hkn⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hkn with h' | h'
          · exact Or.inr ⟨hk, h'⟩
          · exact Or.inl h'
        · rintro (rfl | ⟨hk, hkn⟩)
          · exact ⟨hnK, Nat.lt_succ_self _⟩
          · exact ⟨hk, Nat.lt_succ_of_lt hkn⟩
      have hnot : n ∉ K.filter (· < n) := fun h' => lt_irrefl n (Finset.mem_filter.1 h').2
      have hcard : ((K.filter (· < n + 1)).card : ℝ) = (K.filter (· < n)).card + 1 := by
        rw [hfilt, Finset.card_insert_of_notMem hnot, Nat.cast_succ]
      set A : Set ℂ := ⋃ k ∈ K.filter (· < n), C k with hAdef
      set B : Set ℂ := η '' Icc 0 ((n : ℝ) * h) with hBdef
      have hAB : A ⊆ B := by
        refine iUnion₂_subset fun k hk => image_mono (Icc_subset_Icc (mul_nonneg k.cast_nonneg hh) ?_)
        have : k < n := (Finset.mem_filter.1 hk).2
        have : (k : ℝ) + 1 ≤ n := by exact_mod_cast this
        exact mul_le_mul_of_nonneg_right this hh
      have hBC : B ∪ C n = η '' Icc 0 (((n : ℝ) + 1) * h) := by
        rw [hBdef, hCdef, ← image_union, Icc_union_Icc_eq_Icc hnh
          (mul_le_mul_of_nonneg_right (by linarith) hh)]
      have hAb : Bornology.IsBounded A := hb n
      have hAc : IsPreconnected (A ∪ lowerHalf) :=
        isPreconnected_biUnion_union_lowerHalf _ _ fun k hk => hKc k (Finset.mem_filter.1 hk).1
      have hBb : Bornology.IsBounded B := isBounded_image_Icc hη le_rfl hnT
      have hBc : IsPreconnected (B ∪ lowerHalf) := isPreconnected_image_Icc_zero_union hη hnh hnT
      have hCb : Bornology.IsBounded (C n) := isBounded_image_Icc hη hnh hn1T
      have hCc : IsPreconnected (C n ∪ lowerHalf) := hKc n hnK
      have hinc := hcapFill_union_union_sub_le hAb hAc hBb hBc hCb hCc
      have e1 : hcapFill (A ∪ B ∪ C n) ((hAb.union hBb).union hCb)
          (isPreconnected_union_lowerHalf (isPreconnected_union_lowerHalf hAc hBc) hCc) = 2 * (((n : ℝ) + 1) * h) := by
        rw [hcapFill_congr (show A ∪ B ∪ C n = η '' Icc 0 (((n : ℝ) + 1) * h) by
          rw [union_eq_right.2 hAB, hBC]) _ _ (isBounded_image_Icc hη le_rfl hn1T)
          (isPreconnected_image_Icc_zero_union hη (by positivity) hn1T)]
        exact hcapFill_image_Icc hη hW hW0 (by positivity) hn1T _ _
      have e2 : hcapFill (A ∪ B) (hAb.union hBb) (isPreconnected_union_lowerHalf hAc hBc) = 2 * ((n : ℝ) * h) := by
        rw [hcapFill_congr (show A ∪ B = B from union_eq_right.2 hAB) _ _ hBb hBc]
        exact hcapFill_image_Icc hη hW hW0 hnh hnT _ _
      have e3 : hcapFill (A ∪ C n) (hAb.union hCb) (isPreconnected_union_lowerHalf hAc hCc) =
          hcapFill (⋃ k ∈ K.filter (· < n + 1), C k) (hb (n + 1))
            (isPreconnected_biUnion_union_lowerHalf _ _ fun k hk => hKc k (Finset.mem_filter.1 hk).1) := by
        refine hcapFill_congr ?_ _ _ _ _
        rw [hfilt, Finset.set_biUnion_insert, union_comm]
      rw [e1, e2, e3] at hinc
      rw [hcard]
      change 2 * h * ((K.filter (· < n)).card : ℝ) ≤ hcapFill A hAb hAc at ih
      linarith
    · have hfilt : K.filter (· < n + 1) = K.filter (· < n) := by
        ext k
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hk, hkn⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hkn with h' | h'
          · exact ⟨hk, h'⟩
          · exact absurd (h' ▸ hk) hnK
        · rintro ⟨hk, hkn⟩
          exact ⟨hk, Nat.lt_succ_of_lt hkn⟩
      have e : hcapFill (⋃ k ∈ K.filter (· < n + 1), C k) (hb (n + 1))
            (isPreconnected_biUnion_union_lowerHalf _ _ fun k hk => hKc k (Finset.mem_filter.1 hk).1) =
          hcapFill (⋃ k ∈ K.filter (· < n), C k) (hb n)
            (isPreconnected_biUnion_union_lowerHalf _ _ fun k hk => hKc k (Finset.mem_filter.1 hk).1) :=
        hcapFill_congr (by rw [hfilt]) _ _ _ _
      rw [e, hfilt]
      exact ih

/-- **The boundary time on `[0, T₁]` is at most `(a + 1) δ`** for every `δ ∈ (0, 1]`, with `a` a bound of `|η|` on
`[0, T₁]`. -/
theorem exists_volume_Icc_notMem_H_le (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0)
    {T₁ : ℝ} (hT₁ : 0 ≤ T₁) (hT₁T : T₁ < T) :
    ∃ a : ℝ, 0 < a ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      volume {t | t ∈ Icc 0 T₁ ∧ η t ∉ H} ≤ ENNReal.ofReal ((a + 1) * δ) := by
  classical
  obtain ⟨C, hC⟩ := (hη.isCompact_image hT₁T).isBounded.exists_norm_le
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun δ hδ hδ1 => ?_⟩
  set a := max C 1 with hadef
  have ha : 0 < a := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcont : ContinuousOn η (Icc 0 T₁) := hη.2.1.mono fun _ hu => ⟨hu.1, lt_of_le_of_lt hu.2 hT₁T⟩
  obtain ⟨ε, hε, huc⟩ :=
    Metric.uniformContinuousOn_iff.1 (isCompact_Icc.uniformContinuousOn_of_continuous hcont) δ hδ
  obtain ⟨M, hM⟩ := exists_nat_gt (T₁ / ε)
  set N : ℕ := M + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos M
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set h : ℝ := T₁ / N with hhdef
  have hh : 0 ≤ h := div_nonneg hT₁ hNr.le
  have hNh : (N : ℝ) * h = T₁ := by rw [hhdef]; field_simp
  have hhε : h < ε := by
    rw [hhdef, div_lt_iff₀ hNr]
    have h1 : T₁ < M * ε := by rwa [div_lt_iff₀ hε] at hM
    have h2 : (M : ℝ) * ε ≤ N * ε := mul_le_mul_of_nonneg_right (by rw [hNdef]; push_cast; linarith) hε.le
    linarith
  -- grid intervals
  have hkT : ∀ k < N, ((k : ℝ) + 1) * h ≤ T₁ := fun k hk => by
    rw [← hNh]
    refine mul_le_mul_of_nonneg_right ?_ hh
    exact_mod_cast hk
  set K : Finset ℕ := (Finset.range N).filter
    (fun k => ∃ s ∈ Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h), η s ∉ H) with hKdef
  have hKN : ∀ k ∈ K, k < N := fun k hk => Finset.mem_range.1 (Finset.mem_filter.1 hk).1
  have hKc : ∀ k ∈ K, IsPreconnected (η '' Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h) ∪ lowerHalf) := by
    intro k hk
    obtain ⟨s, hs, hsH⟩ := (Finset.mem_filter.1 hk).2
    refine isPreconnected_union_lowerHalf_of_mem
      (isPreconnected_image_Icc hη (mul_nonneg k.cast_nonneg hh) (lt_of_le_of_lt (hkT k (hKN k hk)) hT₁T))
      (mem_image_of_mem η hs) ?_
    exact not_lt.1 hsH
  -- the bad arcs lie in a thin rectangle
  have hsub : ∀ n : ℕ, (⋃ k ∈ K.filter (· < n), η '' Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h)) ⊆
      {z : ℂ | |z.re| ≤ a ∧ |z.im| ≤ δ} := by
    intro n z hz
    simp only [mem_iUnion, Finset.mem_filter] at hz
    obtain ⟨k, ⟨hk, -⟩, ⟨s', hs', rfl⟩⟩ := hz
    obtain ⟨s, hs, hsH⟩ := (Finset.mem_filter.1 hk).2
    have hk' := hKN k hk
    have hIcc : Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h) ⊆ Icc 0 T₁ :=
      Icc_subset_Icc (mul_nonneg k.cast_nonneg hh) (hkT k hk')
    have hs0 : (η s).im = 0 := le_antisymm (not_lt.1 hsH)
      (hη.im_nonneg hW hW0 (hIcc hs).1 (lt_of_le_of_lt (hIcc hs).2 hT₁T))
    have hdist : dist (η s') (η s) < δ := by
      refine huc s' (hIcc hs') s (hIcc hs) ?_
      rw [Real.dist_eq, abs_lt]
      constructor <;> nlinarith [hs.1, hs.2, hs'.1, hs'.2]
    refine ⟨(Complex.abs_re_le_norm _).trans ((hC _ (mem_image_of_mem η (hIcc hs'))).trans (le_max_left _ _)),
      ?_⟩
    have := (Complex.abs_im_le_norm (η s' - η s)).trans (le_of_lt (by rwa [← dist_eq_norm]))
    rw [Complex.sub_im, hs0, sub_zero] at this
    exact this
  have hb : ∀ n : ℕ, Bornology.IsBounded
      (⋃ k ∈ K.filter (· < n), η '' Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h)) := fun n =>
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := a + δ)).subset fun z hz => by
      have := hsub n hz
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ a + δ := add_le_add this.1 this.2
  have hcount := two_mul_card_le_hcapFill hη hW hW0 hh (by rw [hNh]; exact hT₁T) K hKc hb N le_rfl
  have hfiltN : K.filter (· < N) = K := Finset.filter_true_of_mem hKN
  have hrect := hcapFill_le_of_subset_rect (hb N)
    (isPreconnected_biUnion_union_lowerHalf _ _ fun k hk => hKc k (Finset.mem_filter.1 hk).1) ha hδ (hsub N)
  have hcK : ((K.filter (· < N)).card : ℝ) = K.card := by rw [hfiltN]
  have hcard : (K.card : ℝ) * h ≤ (a + 1) * δ := by
    have := hcount.trans hrect
    rw [hcK] at this
    nlinarith
  -- cover the boundary times by the bad grid intervals
  have hcover : {t | t ∈ Icc 0 T₁ ∧ η t ∉ H} ⊆ ⋃ k ∈ K, Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h) := by
    rintro t ⟨ht, htH⟩
    obtain ⟨k, hk, htk⟩ := exists_mem_grid hN hh (by rwa [hNh])
    exact mem_biUnion (Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, t, htk, htH⟩) htk
  calc volume {t | t ∈ Icc 0 T₁ ∧ η t ∉ H}
      ≤ volume (⋃ k ∈ K, Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h)) := measure_mono hcover
    _ ≤ ∑ k ∈ K, volume (Icc ((k : ℝ) * h) (((k : ℝ) + 1) * h)) := measure_biUnion_finset_le _ _
    _ = ∑ _k ∈ K, ENNReal.ofReal h := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Real.volume_Icc]; congr 1; ring
    _ = ENNReal.ofReal (K.card * h) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((a + 1) * δ) := ENNReal.ofReal_le_ofReal hcard

/-- The boundary time on `[0, T₁]`, `T₁ < T`, is null. -/
theorem volume_Icc_notMem_H (hη : IsLoewnerTraceLT W T η) (hW : Continuous W) (hW0 : W 0 = 0)
    {T₁ : ℝ} (hT₁T : T₁ < T) : volume {t | t ∈ Icc 0 T₁ ∧ η t ∉ H} = 0 := by
  rcases lt_or_ge T₁ 0 with hT₁ | hT₁
  · refine measure_mono_null (fun t ht => ?_) measure_empty
    exact absurd (ht.1.1.trans ht.1.2) (not_le.2 hT₁)
  obtain ⟨a, ha, hle⟩ := exists_volume_Icc_notMem_H_le hη hW hW0 hT₁ hT₁T
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (zero_le)
  set δ : ℝ := min 1 (ε / (a + 1)) with hδdef
  have hδ : 0 < δ := lt_min one_pos (div_pos (by exact_mod_cast hε) (by linarith))
  refine (hle δ hδ (min_le_left _ _)).trans ?_
  rw [zero_add]
  have : (a + 1) * δ ≤ ε := by
    have h1 : δ ≤ ε / (a + 1) := min_le_right _ _
    rwa [le_div_iff₀ (by linarith), mul_comm] at h1
  calc ENNReal.ofReal ((a + 1) * δ) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal this
    _ = ε := ENNReal.ofReal_coe_nnreal

/-- **Lemma 2.5** (specification p. 38): a Loewner trace with a continuous driver spends zero Lebesgue time off the
open half-plane before its horizon, `|{t ∈ [0, T) : η(t) ∉ ℍ}| = 0`. -/
theorem _root_.InteractingSLE.IsLoewnerTraceLT.volume_setOf_notMem_H (hη : IsLoewnerTraceLT W T η)
    (hW : Continuous W) (hW0 : W 0 = 0) : volume {t | t ∈ Ico 0 T ∧ η t ∉ H} = 0 := by
  refine measure_mono_null (t := ⋃ n : ℕ, {t | t ∈ Icc 0 (T - 1 / ((n : ℝ) + 1)) ∧ η t ∉ H}) ?_
    (measure_iUnion_null fun n => volume_Icc_notMem_H hη hW hW0 (by
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith))
  rintro t ⟨ht, htH⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 ht.2)
  exact mem_iUnion.2 ⟨n, ⟨ht.1, by linarith⟩, htH⟩

end Grid

/-! ### The frozen generating trace -/

section Generating

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **Lemma 2.5 for the frozen generating trace** of a driver continuous before its lifetime `ζ`, with `w 0 = 0`:
`|{t ≥ 0 : t < ζ, η(t) ∉ ℍ}| = 0`. -/
theorem _root_.InteractingSLE.IsGeneratingTrace.volume_setOf_notMem_H (hη : IsGeneratingTrace w ζ η)
    (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) :
    volume {t : ℝ | 0 ≤ t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ∧ η t.toNNReal ∉ H} = 0 := by
  classical
  refine measure_mono_null (t := ⋃ q : ℚ, if ENNReal.ofReal q < ζ then
      {t | t ∈ Ico 0 (q : ℝ) ∧ η t.toNNReal ∉ H} else ∅) ?_ (measure_iUnion_null fun q => ?_)
  · rintro t ⟨ht0, htζ, htH⟩
    have htζ' : ENNReal.ofReal t < ζ := htζ
    obtain ⟨q, -, htq, hqζ⟩ := ENNReal.lt_iff_exists_rat_btwn.1 htζ'
    have hqζ' : ENNReal.ofReal q < ζ := hqζ
    refine mem_iUnion.2 ⟨q, ?_⟩
    simp only [hqζ', ↓reduceIte]
    exact ⟨⟨ht0, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht0).1 htq⟩, htH⟩
  · split_ifs with hq
    · have hL := hη.isLoewnerTraceLT hq
      have hW := continuous_frozenDrive_of_lt hwc hq
      have hW0 : frozenDrive w q 0 = 0 := by
        rcases le_or_gt 0 (q : ℝ) with h0 | h0
        · rw [frozenDrive_zero h0, hw0]
        · simp only [frozenDrive, min_eq_right h0.le]
          have : ((q : ℝ)).toNNReal = 0 := Real.toNNReal_of_nonpos h0.le
          rw [this, hw0]
      exact hL.volume_setOf_notMem_H hW hW0
    · exact measure_empty

end Generating

/-! ### Physical tips of a stage read in a conformal chart -/

section Chart

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ} {c : Chart}

/-- `z` is the physical tip at own time `u` of the stage run in the chart `c` by the driver `w`: the radial limit
`lim_{y ↓ 0} c.inv (f_u⁻¹(iy))` (the points of the frozen `Chart.tipSet`). -/
def IsTipPoint (c : Chart) (w : ℝ≥0 → ℝ) (u : ℝ≥0) (z : ℂ) : Prop :=
  Tendsto (fun y : ℝ => c.2.1 (QuantumZipper.fwdMapInv (fun r : ℝ => w r.toNNReal) u (y * Complex.I)))
    (𝓝[>] 0) (𝓝 z)

theorem mem_tipSet_iff {W : ℝ≥0 → ℝ} {s : ℝ≥0∞} {z : ℂ} :
    z ∈ Chart.tipSet c W s ↔ ∃ u : ℝ≥0, (u : ℝ≥0∞) ≤ s ∧ IsTipPoint c W u z := Iff.rfl

/-- **The physical tip is the chart image of the trace point**: in a conformal chart, at an own time `u < ζ` with
`η(u) ∈ ℍ`, the only physical tip point is `c.inv (η u)`. -/
theorem eq_of_isTipPoint (hc : c.IsConformal) (hη : IsGeneratingTrace w ζ η)
    (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ)
    (huH : η u ∈ H) {z : ℂ} (hz : IsTipPoint c w u z) : z = c.2.1 (η u) := by
  have hlim := hη.tendsto_fwdMapInv_mul_I hwc hw0 hu
  have hcont : ContinuousAt c.2.1 (η u) :=
    (hc.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds huH)).continuousAt
  exact tendsto_nhds_unique hz (hcont.tendsto.comp hlim)

/-- **A physical tip over an interior trace point is interior.** -/
theorem mem_H_of_isTipPoint (hc : c.IsConformal) (hη : IsGeneratingTrace w ζ η)
    (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < ζ)
    (huH : η u ∈ H) {z : ℂ} (hz : IsTipPoint c w u z) : z ∈ H := by
  rw [eq_of_isTipPoint hc hη hwc hw0 hu huH hz]
  exact hc.2.1 huH

/-- **Lemma 2.5 in a conformal chart** (the form used for the pieces of a concatenated flow, GB9a p. 527): the own
times before the lifetime at which the stage has a physical tip point off `ℍ` form a Lebesgue-null set. -/
theorem volume_setOf_isTipPoint_notMem_H (hc : c.IsConformal) (hη : IsGeneratingTrace w ζ η)
    (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) :
    volume {u : ℝ | 0 ≤ u ∧ ((u.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ∧
      ∃ z, IsTipPoint c w u.toNNReal z ∧ z ∉ H} = 0 := by
  refine measure_mono_null (fun u hu => ?_) (hη.volume_setOf_notMem_H hwc hw0)
  obtain ⟨hu0, huζ, z, hz, hzH⟩ := hu
  refine ⟨hu0, huζ, fun huH => hzH ?_⟩
  exact mem_H_of_isTipPoint hc hη hwc hw0 huζ huH hz

end Chart

end Lemma25

end InteractingSLE
