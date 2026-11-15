/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma78MeanWordGeom

/-!
# Lemma 7.8's boundary word

Packet PROVE-PRIMEEND2, item (a) of `planning/handoffs/PROVE-PRIMEEND.md`. Lemma 7.8 (p. 290) and Aux. 78: in the
first-contact chart `φ : D → ℍ` the conditional mean is `𝔤 ∘ φ − χ arg φ′`, `𝔤` the bounded harmonic extension of
the original data on the images of the exposed original real boundary, `−λ − θ₂χ` on the image `(L, 0)` of the exposed
left side of the second prefix and `λ − θ₁χ` on the image `(0, R)` of the exposed right side of the first one
(PROVE-PRIMEEND §Details 5 checks this word against Aux. 78/80).

Here the word is built from an original sorted word `c₀` (positions `j₀ < ⋯ < j_{N−1}`, heights `q₀, …, q_N`) and the
two side heights:

* positions `ℓ(j₀), …, ℓ(j_{k−1})` (the original jumps left of the base `a`, `k = #{j_i < a}`), then `L, 0, R`, then
  `ℓ(j_l), …, ℓ(j_{N−1})` (the original jumps right of the base `b`, `l = #{j_i ≤ b}`);
* heights `q₀, …, q_k`, then `hL` on `(L, 0)` and `hR` on `(0, R)`, then `q_l, …, q_N`.

## Main results

* `PairData.word`: the word;
* `PairData.IsMeasGood.word_isSorted`: it is sorted on the contact event;
* `PairData.IsMeasGood.word_fn_of_lt_wordL`, `word_fn_of_wordR_lt`: off `[L, R]` its datum is the original datum at
  `ψ(w)`; `word_fn_of_mem_Ioo_left`, `word_fn_of_mem_Ioo_right`: the side heights on `(L, 0)` and `(0, R)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace Restart

/-! ### Counting below a threshold -/

/-- For a strictly increasing finite sequence and a downward-closed condition, the indices satisfying the condition
are an initial segment, of length their number. -/
theorem lt_card_filter_iff {p : ℕ → ℝ} {N : ℕ} (hp : StrictMonoOn p (Iio N)) {P : ℝ → Prop} [DecidablePred P]
    (hP : ∀ y y', y' ≤ y → P y → P y') {i : ℕ} (hi : i < N) :
    i < ((Finset.range N).filter fun m => P (p m)).card ↔ P (p i) := by
  constructor
  · intro h
    by_contra hy
    have hsub : (Finset.range N).filter (fun m => P (p m)) ⊆ Finset.range i := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_range] at hm
      rw [Finset.mem_range]
      by_contra hmi
      exact hy (hP _ _ (hp.monotoneOn hi hm.1 (not_lt.1 hmi)) hm.2)
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  · intro h
    have hsub : Finset.range (i + 1) ⊆ (Finset.range N).filter (fun m => P (p m)) := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hP _ _ (hp.monotoneOn (show m < N by omega) hi (by omega)) h⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega

theorem card_filter_le_range {N : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range N).filter P).card ≤ N :=
  (Finset.card_filter_le _ _).trans (Finset.card_range N).le

/-- The index of a word at `w` is `t` when exactly the positions of index `< t` lie strictly left of `w`. -/
theorem BoundaryWord.index_eq_of_iff {c : BoundaryWord} {w : ℝ} {t : ℕ} (ht : t ≤ c.1)
    (h : ∀ i < c.1, c.2.1 i < w ↔ i < t) : c.index w = t := by
  unfold BoundaryWord.index
  have e : (Finset.range c.1).filter (fun i => c.2.1 i < w) = Finset.range t := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, hw⟩; exact (h i hi).1 hw
    · intro hi; exact ⟨by omega, (h i (by omega)).2 hi⟩
  rw [e, Finset.card_range]

/-! ### The word -/

section Word

variable {Ω : Type*} [MeasurableSpace Ω] {d : PairData Ω}

/-- The number of original jumps strictly left of the base `a`. -/
def PairData.wordK (d : PairData Ω) (c₀ : BoundaryWord) (ω : Ω) : ℕ :=
  ((Finset.range c₀.1).filter fun i => c₀.2.1 i < d.baseL ω).card

/-- The number of original jumps at most the right end `b` of the base. -/
def PairData.wordLe (d : PairData Ω) (c₀ : BoundaryWord) (ω : Ω) : ℕ :=
  ((Finset.range c₀.1).filter fun i => c₀.2.1 i ≤ d.baseR ω).card

open scoped Classical in
/-- **Lemma 7.8's boundary word** in the first-contact chart, from the original word `c₀` and the side heights
`hL` (on `(L, 0)`) and `hR` (on `(0, R)`). -/
def PairData.word (d : PairData Ω) (c₀ : BoundaryWord) (hL hR : ℝ) (ω : Ω) : BoundaryWord :=
  let k := d.wordK c₀ ω
  let l := d.wordLe c₀ ω
  (k + 3 + (c₀.1 - l),
    fun i => if i < k then d.bdry ω (c₀.2.1 i) else if i = k then d.wordL ω else if i = k + 1 then 0
      else if i = k + 2 then d.wordR ω else d.bdry ω (c₀.2.1 (i - (k + 3) + l)),
    fun i => if i ≤ k then c₀.2.2 i else if i = k + 1 then hL else if i = k + 2 then hR
      else c₀.2.2 (i - (k + 3) + l))

variable (hd : d.IsMeasGood) {ω : Ω} (hE : ω ∈ d.E) {c₀ : BoundaryWord} (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
include hd hE hc₀

omit [MeasurableSpace Ω] hd hE in
theorem PairData.lt_wordK_iff {i : ℕ} (hi : i < c₀.1) :
    i < d.wordK c₀ ω ↔ c₀.2.1 i < d.baseL ω :=
  lt_card_filter_iff hc₀ (P := fun y => y < d.baseL ω) (fun _ _ h1 h2 => lt_of_le_of_lt h1 h2) hi

omit [MeasurableSpace Ω] hd hE in
theorem PairData.lt_wordLe_iff {i : ℕ} (hi : i < c₀.1) :
    i < d.wordLe c₀ ω ↔ c₀.2.1 i ≤ d.baseR ω :=
  lt_card_filter_iff hc₀ (P := fun y => y ≤ d.baseR ω) (fun _ _ h1 h2 => h1.trans h2) hi

omit hc₀ in
theorem PairData.wordK_le_wordLe : d.wordK c₀ ω ≤ d.wordLe c₀ ω := by
  unfold PairData.wordK PairData.wordLe
  refine Finset.card_le_card fun i => ?_
  simp only [Finset.mem_filter]
  exact fun ⟨h1, h2⟩ => ⟨h1, h2.le.trans (hd.baseL_le_baseR hE)⟩

variable (hL hR : ℝ)

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_fst : (d.word c₀ hL hR ω).1 = d.wordK c₀ ω + 3 + (c₀.1 - d.wordLe c₀ ω) := rfl

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_pos_of_lt {i : ℕ} (hi : i < d.wordK c₀ ω) :
    (d.word c₀ hL hR ω).2.1 i = d.bdry ω (c₀.2.1 i) := by
  simp [PairData.word, hi]

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_pos_k : (d.word c₀ hL hR ω).2.1 (d.wordK c₀ ω) = d.wordL ω := by
  simp [PairData.word]

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_pos_k1 : (d.word c₀ hL hR ω).2.1 (d.wordK c₀ ω + 1) = 0 := by
  simp [PairData.word]

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_pos_k2 : (d.word c₀ hL hR ω).2.1 (d.wordK c₀ ω + 2) = d.wordR ω := by
  simp [PairData.word]

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_pos_of_ge {i : ℕ} (hi : d.wordK c₀ ω + 3 ≤ i) :
    (d.word c₀ hL hR ω).2.1 i = d.bdry ω (c₀.2.1 (i - (d.wordK c₀ ω + 3) + d.wordLe c₀ ω)) := by
  have h1 : ¬ i < d.wordK c₀ ω := by omega
  have h2 : i ≠ d.wordK c₀ ω := by omega
  have h3 : i ≠ d.wordK c₀ ω + 1 := by omega
  have h4 : i ≠ d.wordK c₀ ω + 2 := by omega
  simp [PairData.word, h1, h2, h3, h4]

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_ht_of_le {i : ℕ} (hi : i ≤ d.wordK c₀ ω) : (d.word c₀ hL hR ω).2.2 i = c₀.2.2 i := by
  simp [PairData.word, hi]

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_ht_k1 : (d.word c₀ hL hR ω).2.2 (d.wordK c₀ ω + 1) = hL := by
  simp [PairData.word]

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_ht_k2 : (d.word c₀ hL hR ω).2.2 (d.wordK c₀ ω + 2) = hR := by
  simp [PairData.word]

omit [MeasurableSpace Ω] hd hE hc₀ in
theorem PairData.word_ht_of_ge {i : ℕ} (hi : d.wordK c₀ ω + 3 ≤ i) :
    (d.word c₀ hL hR ω).2.2 i = c₀.2.2 (i - (d.wordK c₀ ω + 3) + d.wordLe c₀ ω) := by
  have h1 : ¬ i ≤ d.wordK c₀ ω := by omega
  have h3 : i ≠ d.wordK c₀ ω + 1 := by omega
  have h4 : i ≠ d.wordK c₀ ω + 2 := by omega
  simp [PairData.word, h1, h3, h4]

/-- The positions of the left block lie left of `L`. -/
theorem PairData.IsMeasGood.word_pos_lt_wordL {i : ℕ} (hi : i < d.wordK c₀ ω) :
    (d.word c₀ hL hR ω).2.1 i < d.wordL ω := by
  have hiN : i < c₀.1 := lt_of_lt_of_le hi (card_filter_le_range _)
  rw [PairData.word_pos_of_lt hL hR hi]
  exact hd.bdry_lt_wordL hE ((PairData.lt_wordK_iff hc₀ hiN).1 hi)

/-- The positions of the right block lie right of `R`. -/
theorem PairData.IsMeasGood.wordR_lt_word_pos {i : ℕ} (hi : d.wordK c₀ ω + 3 ≤ i)
    (hin : i < (d.word c₀ hL hR ω).1) : d.wordR ω < (d.word c₀ hL hR ω).2.1 i := by
  have hl := PairData.wordK_le_wordLe hd hE (c₀ := c₀)
  rw [PairData.word_fst] at hin
  have hmN : i - (d.wordK c₀ ω + 3) + d.wordLe c₀ ω < c₀.1 := by omega
  rw [PairData.word_pos_of_ge hL hR hi]
  refine hd.wordR_lt_bdry hE (not_le.1 fun h => ?_)
  have := (PairData.lt_wordLe_iff hc₀ hmN).2 h
  omega

/-- **The word is sorted** on the contact event. -/
theorem PairData.IsMeasGood.word_isSorted : (d.word c₀ hL hR ω).IsSorted := by
  intro i j hij hjn
  set k := d.wordK c₀ ω with hk
  set c := d.word c₀ hL hR ω with hc
  have hL0 := hd.wordL_nonpos hE
  have hR0 := hd.wordR_nonneg hE
  have hlN : d.wordLe c₀ ω ≤ c₀.1 := card_filter_le_range _
  have hkl := PairData.wordK_le_wordLe hd hE (c₀ := c₀)
  -- lower bounds for `j ≥ k`
  have hlow : ∀ m, k ≤ m → m < c.1 → d.wordL ω ≤ c.2.1 m := by
    intro m hm hmn
    rcases hm.lt_or_eq with hm | rfl
    · rcases Nat.lt_or_ge m (k + 3) with h3 | h3
      · obtain rfl | rfl : m = k + 1 ∨ m = k + 2 := by omega
        · rw [hc, PairData.word_pos_k1]; exact hL0
        · rw [hc, PairData.word_pos_k2]; linarith
      · linarith [hd.wordR_lt_word_pos hE hc₀ hL hR h3 hmn]
    · rw [hc, PairData.word_pos_k]
  rcases Nat.lt_or_ge j k with hjk | hjk
  · -- both in the left block
    have hiN : i < c₀.1 := lt_of_lt_of_le (lt_of_le_of_lt hij hjk) (card_filter_le_range _)
    have hjN : j < c₀.1 := lt_of_lt_of_le hjk (card_filter_le_range _)
    rw [hc, PairData.word_pos_of_lt hL hR (lt_of_le_of_lt hij hjk), PairData.word_pos_of_lt hL hR hjk]
    rcases hij.lt_or_eq with hlt | rfl
    · exact (hd.strictMonoOn_bdry_Iio hE ((PairData.lt_wordK_iff hc₀ hiN).1 (lt_of_le_of_lt hij hjk))
        ((PairData.lt_wordK_iff hc₀ hjN).1 hjk) (hc₀ hiN hjN hlt)).le
    · exact le_rfl
  rcases Nat.lt_or_ge i (k + 3) with hi3 | hi3
  · rcases Nat.lt_or_ge i k with hik | hik
    · exact (hd.word_pos_lt_wordL hE hc₀ hL hR hik).le.trans (hlow j hjk hjn)
    · obtain rfl | rfl | rfl : i = k ∨ i = k + 1 ∨ i = k + 2 := by omega
      · rw [hc, PairData.word_pos_k]; exact hlow j hjk hjn
      · rw [hc, PairData.word_pos_k1]
        rcases Nat.lt_or_ge j (k + 3) with hj3 | hj3
        · obtain rfl | rfl : j = k + 1 ∨ j = k + 2 := by omega
          · rw [PairData.word_pos_k1]
          · rw [PairData.word_pos_k2]; exact hR0
        · linarith [hd.wordR_lt_word_pos hE hc₀ hL hR hj3 hjn]
      · rw [hc, PairData.word_pos_k2]
        rcases Nat.lt_or_ge j (k + 3) with hj3 | hj3
        · obtain rfl : j = k + 2 := by omega
          rw [PairData.word_pos_k2]
        · exact (hd.wordR_lt_word_pos hE hc₀ hL hR hj3 hjn).le
  · -- both in the right block
    have hin : i < c.1 := lt_of_le_of_lt hij hjn
    rw [hc, PairData.word_fst] at hin hjn
    rw [hc, PairData.word_pos_of_ge hL hR hi3, PairData.word_pos_of_ge hL hR (hi3.trans hij)]
    set mi := i - (k + 3) + d.wordLe c₀ ω
    set mj := j - (k + 3) + d.wordLe c₀ ω
    have hmiN : mi < c₀.1 := by omega
    have hmjN : mj < c₀.1 := by omega
    have hgt : ∀ m, d.wordLe c₀ ω ≤ m → (hm : m < c₀.1) → d.baseR ω < c₀.2.1 m := fun m hm hmN =>
      not_le.1 fun h => by have := (PairData.lt_wordLe_iff hc₀ hmN).2 h; omega
    rcases hij.lt_or_eq with hlt | rfl
    · exact (hd.strictMonoOn_bdry_Ioi hE (hgt mi (by omega) hmiN) (hgt mj (by omega) hmjN)
        (hc₀ hmiN hmjN (by omega))).le
    · exact le_rfl

/-- **Left of `L` the word's datum is the original datum at the chart preimage** `ψ(w)` (an untouched real point
left of the base). -/
theorem PairData.IsMeasGood.word_fn_of_lt_wordL {w : ℝ} (hw : w < d.wordL ω) :
    (d.word c₀ hL hR ω).fn w = c₀.fn (d.inv ω w).re := by
  obtain ⟨hxa, -, hxw⟩ := hd.inv_of_lt_wordL hE hw
  set x := (d.inv ω w).re with hx
  set k := d.wordK c₀ ω with hk
  set t := c₀.index x with ht
  have htk : t ≤ k := by
    by_contra h
    have hkN : k < c₀.1 := lt_of_lt_of_le (not_le.1 h) (c₀.index_le x)
    have := (BoundaryWord.lt_index_iff hc₀ hkN).1 (not_le.1 h)
    have := (PairData.lt_wordK_iff hc₀ hkN).2 (this.trans hxa)
    omega
  have hidx : (d.word c₀ hL hR ω).index w = t := by
    refine BoundaryWord.index_eq_of_iff (htk.trans (by rw [PairData.word_fst]; omega)) fun i hi => ?_
    rcases Nat.lt_or_ge i k with hik | hik
    · have hiN : i < c₀.1 := lt_of_lt_of_le hik (card_filter_le_range _)
      have hia := (PairData.lt_wordK_iff hc₀ hiN).1 hik
      rw [PairData.word_pos_of_lt hL hR hik, ← hxw, (hd.strictMonoOn_bdry_Iio hE).lt_iff_lt hia hxa,
        BoundaryWord.lt_index_iff hc₀ hiN]
    · constructor
      · intro h
        exfalso
        have hle : d.wordL ω ≤ (d.word c₀ hL hR ω).2.1 i := by
          rcases hik.lt_or_eq with hik | rfl
          · rcases Nat.lt_or_ge i (k + 3) with h3 | h3
            · obtain rfl | rfl : i = k + 1 ∨ i = k + 2 := by omega
              · rw [PairData.word_pos_k1]; exact hd.wordL_nonpos hE
              · rw [PairData.word_pos_k2]; linarith [hd.wordL_nonpos hE, hd.wordR_nonneg hE]
            · linarith [hd.wordR_lt_word_pos hE hc₀ hL hR h3 hi, hd.wordL_nonpos hE, hd.wordR_nonneg hE]
          · rw [PairData.word_pos_k]
        linarith
      · intro h; omega
  unfold BoundaryWord.fn
  rw [hidx, PairData.word_ht_of_le hL hR htk]

/-- **Right of `R` the word's datum is the original datum at the chart preimage** `ψ(w)`. -/
theorem PairData.IsMeasGood.word_fn_of_wordR_lt {w : ℝ} (hw : d.wordR ω < w) :
    (d.word c₀ hL hR ω).fn w = c₀.fn (d.inv ω w).re := by
  obtain ⟨hxb, -, hxw⟩ := hd.inv_of_wordR_lt hE hw
  set x := (d.inv ω w).re with hx
  set k := d.wordK c₀ ω with hk
  set l := d.wordLe c₀ ω with hl
  obtain ⟨sx, hsx⟩ : ∃ s, c₀.index x = s := ⟨_, rfl⟩
  have hlN : l ≤ c₀.1 := card_filter_le_range _
  have hls : l ≤ sx := by
    by_contra h
    have hsN : sx < c₀.1 := lt_of_lt_of_le (not_le.1 h) hlN
    have := (PairData.lt_wordLe_iff hc₀ hsN).1 (not_le.1 h)
    have := (BoundaryWord.lt_index_iff hc₀ hsN).2 (lt_of_le_of_lt this hxb)
    omega
  have hsN : sx ≤ c₀.1 := hsx ▸ c₀.index_le x
  have hgt : ∀ m, l ≤ m → (hm : m < c₀.1) → d.baseR ω < c₀.2.1 m := fun m hm hmN =>
    not_le.1 fun h => by have := (PairData.lt_wordLe_iff hc₀ hmN).2 h; omega
  have hidx : (d.word c₀ hL hR ω).index w = k + 3 + (sx - l) := by
    refine BoundaryWord.index_eq_of_iff (by rw [PairData.word_fst]; omega) fun i hi => ?_
    rw [PairData.word_fst] at hi
    rcases Nat.lt_or_ge i (k + 3) with h3 | h3
    · refine iff_of_true ?_ (by omega)
      rcases Nat.lt_or_ge i k with hik | hik
      · linarith [hd.word_pos_lt_wordL hE hc₀ hL hR hik, hd.wordL_nonpos hE, hd.wordR_nonneg hE]
      · obtain rfl | rfl | rfl : i = k ∨ i = k + 1 ∨ i = k + 2 := by omega
        · rw [PairData.word_pos_k]; linarith [hd.wordL_nonpos hE, hd.wordR_nonneg hE]
        · rw [PairData.word_pos_k1]; linarith [hd.wordR_nonneg hE]
        · rw [PairData.word_pos_k2]; exact hw
    · have hmN : i - (k + 3) + l < c₀.1 := by omega
      rw [PairData.word_pos_of_ge hL hR h3, ← hxw,
        (hd.strictMonoOn_bdry_Ioi hE).lt_iff_lt (hgt _ (by omega) hmN) hxb, ← BoundaryWord.lt_index_iff hc₀ hmN,
        hsx]
      omega
  have hge : d.wordK c₀ ω + 3 ≤ k + 3 + (sx - l) := by omega
  unfold BoundaryWord.fn
  rw [hidx, PairData.word_ht_of_ge hL hR hge, hsx, ← hk, ← hl,
    show k + 3 + (sx - l) - (k + 3) + l = sx by omega]

/-- **On `(L, 0)` the word's datum is the left side height.** -/
theorem PairData.IsMeasGood.word_fn_of_mem_Ioo_left {w : ℝ} (h1 : d.wordL ω < w) (h2 : w < 0) :
    (d.word c₀ hL hR ω).fn w = hL := by
  set k := d.wordK c₀ ω with hk
  have hidx : (d.word c₀ hL hR ω).index w = k + 1 := by
    refine BoundaryWord.index_eq_of_iff (by rw [PairData.word_fst]; omega) fun i hi => ?_
    rcases Nat.lt_or_ge i k with hik | hik
    · exact iff_of_true ((hd.word_pos_lt_wordL hE hc₀ hL hR hik).trans h1) (by omega)
    rcases Nat.lt_or_ge i (k + 3) with h3 | h3
    · obtain rfl | rfl | rfl : i = k ∨ i = k + 1 ∨ i = k + 2 := by omega
      · rw [PairData.word_pos_k]; exact iff_of_true h1 (by omega)
      · rw [PairData.word_pos_k1]; exact iff_of_false (by linarith) (by omega)
      · rw [PairData.word_pos_k2]; exact iff_of_false (by linarith [hd.wordR_nonneg hE]) (by omega)
    · exact iff_of_false (by linarith [hd.wordR_lt_word_pos hE hc₀ hL hR h3 hi, hd.wordR_nonneg hE]) (by omega)
  unfold BoundaryWord.fn
  rw [hidx, PairData.word_ht_k1]

/-- **On `(0, R)` the word's datum is the right side height.** -/
theorem PairData.IsMeasGood.word_fn_of_mem_Ioo_right {w : ℝ} (h1 : 0 < w) (h2 : w < d.wordR ω) :
    (d.word c₀ hL hR ω).fn w = hR := by
  set k := d.wordK c₀ ω with hk
  have hidx : (d.word c₀ hL hR ω).index w = k + 2 := by
    refine BoundaryWord.index_eq_of_iff (by rw [PairData.word_fst]; omega) fun i hi => ?_
    rcases Nat.lt_or_ge i k with hik | hik
    · exact iff_of_true (by linarith [hd.word_pos_lt_wordL hE hc₀ hL hR hik, hd.wordL_nonpos hE]) (by omega)
    rcases Nat.lt_or_ge i (k + 3) with h3 | h3
    · obtain rfl | rfl | rfl : i = k ∨ i = k + 1 ∨ i = k + 2 := by omega
      · rw [PairData.word_pos_k]; exact iff_of_true (by linarith [hd.wordL_nonpos hE]) (by omega)
      · rw [PairData.word_pos_k1]; exact iff_of_true h1 (by omega)
      · rw [PairData.word_pos_k2]; exact iff_of_false (by linarith) (by omega)
    · exact iff_of_false (by linarith [hd.wordR_lt_word_pos hE hc₀ hL hR h3 hi]) (by omega)
  unfold BoundaryWord.fn
  rw [hidx, PairData.word_ht_k2]

/-- An original jump seen from left of `L` is a jump of the word. -/
theorem PairData.IsMeasGood.mem_word_jumps_of_lt_wordL {w : ℝ} (hw : w < d.wordL ω)
    (hj : (d.inv ω w).re ∈ c₀.jumps) : w ∈ (d.word c₀ hL hR ω).jumps := by
  obtain ⟨hxa, -, hxw⟩ := hd.inv_of_lt_wordL hE hw
  obtain ⟨m, hm, hmx⟩ := BoundaryWord.mem_jumps.1 hj
  have hmk : m < d.wordK c₀ ω := (PairData.lt_wordK_iff hc₀ hm).2 (hmx ▸ hxa)
  refine BoundaryWord.mem_jumps.2 ⟨m, by rw [PairData.word_fst]; omega, ?_⟩
  rw [PairData.word_pos_of_lt hL hR hmk, hmx, hxw]

/-- An original jump seen from right of `R` is a jump of the word. -/
theorem PairData.IsMeasGood.mem_word_jumps_of_wordR_lt {w : ℝ} (hw : d.wordR ω < w)
    (hj : (d.inv ω w).re ∈ c₀.jumps) : w ∈ (d.word c₀ hL hR ω).jumps := by
  obtain ⟨hxb, -, hxw⟩ := hd.inv_of_wordR_lt hE hw
  obtain ⟨m, hm, hmx⟩ := BoundaryWord.mem_jumps.1 hj
  have hlm : d.wordLe c₀ ω ≤ m := by
    by_contra h
    have := (PairData.lt_wordLe_iff hc₀ hm).1 (not_le.1 h)
    rw [hmx] at this
    linarith
  have hkl := PairData.wordK_le_wordLe hd hE (c₀ := c₀)
  refine BoundaryWord.mem_jumps.2 ⟨m - d.wordLe c₀ ω + (d.wordK c₀ ω + 3), by rw [PairData.word_fst]; omega, ?_⟩
  rw [PairData.word_pos_of_ge hL hR (by omega)]
  have : m - d.wordLe c₀ ω + (d.wordK c₀ ω + 3) - (d.wordK c₀ ω + 3) + d.wordLe c₀ ω = m := by omega
  rw [this, hmx, hxw]

end Word

end Restart

end InteractingSLE
