/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76GWord

/-!
# The zone word of a touching retained pair

Packet PROVE-T15-RET4 (Aux. lemmas 85–86, supplement pp. 299–301). When the two retained prefixes meet, the outer
boundary (OF2) of their union has no untouched real zone between them: in the retained chart (second tip at `0`) it is

* the untouched real points left of the second base (chart points left of `L₂`),
* the second prefix's left side `(L₂, 0)` and right side `(0, J)` up to the junction `J` over the last common point,
* the first prefix's left side `(J, M₁)` and right side `(M₁, R₁)`,
* the untouched real points right of the first base (chart points right of `R₁`).

The word is PROVE-LEMMA76G's zone word `Sec7.Lemma76G.ZW.word` with the junction doubled (`R₂ = L₁ = J`) and an empty
middle block (`a₁ ≤ b₂`, so no original jump is read between the bases). `Sec7.Lemma76G.ZW.Good` demands a nonempty
middle zone, so the order facts are re-proved here under `GoodT` (touching zone data):

* `GoodT.word_isSorted`: the word is sorted (positions may repeat at the junction);
* `GoodT.fn_zone₀`, `GoodT.fn_zone₂`: on the two untouched zones the datum is the original one at the preimage;
* `GoodT.fn_side₁` … `GoodT.fn_side₄`: the four side heights `g₁` on `(L₂, M₂)`, `g₂` on `(M₂, R₂)`, `g₃` on
  `(L₁, M₁)`, `g₄` on `(M₁, R₁)`;
* `GoodT.pos_cases`: every position is one of `L₂, M₂, R₂, L₁, M₁, R₁` or the chart point of an original jump of one
  of the two untouched zones.

The builder `Sec7.Lemma76G.zbuild` with equal middle counts is this word truncated (`zbuild` reads no middle jump), so
the measurable word of PROVE-LEMMA76G applies verbatim once the five chart points are measurable.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace RLC

namespace RetTouch

open Restart Sec7 Sec7.Lemma76G Sec7.Lemma76G.ZW

/-- **The order hypotheses on touching zone data**: the zone word of `Sec7.Lemma76G.ZW` with an empty middle block
(`a₁ ≤ b₂`, so no original jump is read between the bases) and a possibly degenerate junction (`R₂ ≤ L₁`). -/
structure GoodT (z : ZW) : Prop where
  a₂_le_b₁ : z.a₂ ≤ z.b₁
  a₁_le_b₂ : z.a₁ ≤ z.b₂
  mono₀ : StrictMonoOn z.T (Iio z.a₂)
  mono₂ : StrictMonoOn z.T (Ioi z.b₁)
  T₀_lt : ∀ x < z.a₂, z.T x < z.L₂
  L₂_le : z.L₂ ≤ z.M₂
  M₂_le : z.M₂ ≤ z.R₂
  R₂_le : z.R₂ ≤ z.L₁
  L₁_le : z.L₁ ≤ z.M₁
  M₁_le : z.M₁ ≤ z.R₁
  lt_T₂ : ∀ x, z.b₁ < x → z.R₁ < z.T x

namespace GoodT

variable {z : ZW} {c₀ : BoundaryWord} {g₁ g₂ g₃ g₄ : ℝ} (hz : GoodT z)
include hz

/-! ### Counting -/

theorem k₃_le_k₂ : z.k₃ c₀ ≤ z.k₂ c₀ := by
  unfold ZW.k₂ ZW.k₃ cntLt cntLe
  exact Finset.card_le_card fun i => by
    simp only [Finset.mem_filter]
    exact fun ⟨h1, h2⟩ => ⟨h1, h2.le.trans hz.a₁_le_b₂⟩

theorem k₁_le_k₄ : z.k₁ c₀ ≤ z.k₄ c₀ := by
  unfold ZW.k₁ ZW.k₄ cntLt cntLe
  exact Finset.card_le_card fun i => by
    simp only [Finset.mem_filter]
    exact fun ⟨h1, h2⟩ => ⟨h1, h2.le.trans hz.a₂_le_b₁⟩

/-- The middle block is empty. -/
theorem m_eq : z.m c₀ = z.k₁ c₀ + 3 := by
  have := hz.k₃_le_k₂ (c₀ := c₀)
  unfold ZW.m
  omega

/-! ### The order of the positions -/

section Order

variable (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
include hc₀

theorem pos_lt_L₂ {i : ℕ} (hi : i < z.k₁ c₀) : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i < z.L₂ := by
  have hiN : i < c₀.1 := lt_of_lt_of_le hi (card_filter_le_range _)
  rw [pos_of_lt hi]
  exact hz.T₀_lt _ ((lt_k₁_iff hc₀ hiN).1 hi)

theorem R₁_lt_pos {i : ℕ} (h1 : z.m c₀ + 3 ≤ i) (hi : i < (z.word c₀ g₁ g₂ g₃ g₄).1) :
    z.R₁ < (z.word c₀ g₁ g₂ g₃ g₄).2.1 i := by
  rw [pos_right h1]
  exact hz.lt_T₂ _ (right_mem hc₀ h1 hi).1

/-- The positions up to `m` are at most `L₁`. -/
theorem pos_le_L₁ {i : ℕ} (hi : i ≤ z.m c₀) : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i ≤ z.L₁ := by
  have hm := hz.m_eq (c₀ := c₀)
  rcases hi.lt_or_eq with hi | rfl
  · rcases Nat.lt_or_ge i (z.k₁ c₀) with h1 | h1
    · linarith [hz.pos_lt_L₂ hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) h1, hz.L₂_le, hz.M₂_le, hz.R₂_le]
    · obtain rfl | rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 ∨ i = z.k₁ c₀ + 2 := by omega
      · rw [pos_k₁]; linarith [hz.L₂_le, hz.M₂_le, hz.R₂_le]
      · rw [pos_k₁1]; linarith [hz.M₂_le, hz.R₂_le]
      · rw [pos_k₁2]; exact hz.R₂_le
  · rw [pos_m]

/-- **The touching word is sorted.** -/
theorem word_isSorted : (z.word c₀ g₁ g₂ g₃ g₄).IsSorted := by
  intro i j hij hjn
  rcases hij.lt_or_eq with hlt | rfl
  swap
  · exact le_rfl
  have hin : i < (z.word c₀ g₁ g₂ g₃ g₄).1 := lt_trans hlt hjn
  have hm := hz.m_eq (c₀ := c₀)
  -- `j` in the right block
  rcases Nat.lt_or_ge j (z.m c₀ + 3) with hj3 | hj3
  swap
  · rcases Nat.lt_or_ge i (z.m c₀ + 3) with hi3 | hi3
    · have hjR := hz.R₁_lt_pos hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hj3 hjn
      rcases Nat.lt_or_ge i (z.m c₀ + 1) with hi1 | hi1
      · linarith [hz.pos_le_L₁ hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
          hz.L₁_le, hz.M₁_le]
      · obtain rfl | rfl : i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by omega
        · rw [pos_m1]; linarith [hz.M₁_le]
        · rw [pos_m2]; exact hjR.le
    · obtain ⟨hmi, hiN⟩ := right_mem hc₀ hi3 hin
      obtain ⟨hmj, hjN⟩ := right_mem hc₀ hj3 hjn
      rw [pos_right hi3, pos_right hj3]
      exact (hz.mono₂ hmi hmj (hc₀ hiN hjN (by omega))).le
  -- `j ∈ {m + 1, m + 2}`
  rcases Nat.lt_or_ge j (z.m c₀ + 1) with hj1 | hj1
  swap
  · have hiL : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i ≤ (z.word c₀ g₁ g₂ g₃ g₄).2.1 (z.m c₀ + 1) := by
      rw [pos_m1]
      rcases Nat.lt_or_ge i (z.m c₀ + 1) with hi1 | hi1
      · linarith [hz.pos_le_L₁ hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
          hz.L₁_le]
      · obtain rfl : i = z.m c₀ + 1 := by omega
        rw [pos_m1]
    obtain rfl | rfl : j = z.m c₀ + 1 ∨ j = z.m c₀ + 2 := by omega
    · exact hiL
    · rw [pos_m2]; rw [pos_m1] at hiL; linarith [hz.M₁_le]
  -- `j = m`
  rcases (show j ≤ z.m c₀ by omega).lt_or_eq with hjm | rfl
  swap
  · rw [pos_m]; exact hz.pos_le_L₁ hc₀ (show i ≤ z.m c₀ by omega)
  -- `j < m = k₁ + 3`
  rcases Nat.lt_or_ge j (z.k₁ c₀) with hj0 | hj0
  · have hjN : j < c₀.1 := lt_of_lt_of_le hj0 (card_filter_le_range _)
    have hiN : i < c₀.1 := lt_trans hlt hjN
    rw [pos_of_lt (lt_trans hlt hj0), pos_of_lt hj0]
    exact (hz.mono₀ ((lt_k₁_iff hc₀ hiN).1 (lt_trans hlt hj0)) ((lt_k₁_iff hc₀ hjN).1 hj0)
      (hc₀ hiN hjN hlt)).le
  · obtain rfl | rfl | rfl : j = z.k₁ c₀ ∨ j = z.k₁ c₀ + 1 ∨ j = z.k₁ c₀ + 2 := by omega
    · rw [pos_k₁]
      rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
      · exact (hz.pos_lt_L₂ hc₀ hi0).le
      · exfalso; omega
    · rw [pos_k₁1]
      rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
      · linarith [hz.pos_lt_L₂ hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hi0, hz.L₂_le]
      · obtain rfl : i = z.k₁ c₀ := by omega
        rw [pos_k₁]; exact hz.L₂_le
    · rw [pos_k₁2]
      rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
      · linarith [hz.pos_lt_L₂ hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hi0, hz.L₂_le, hz.M₂_le]
      · obtain rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 := by omega
        · rw [pos_k₁]; linarith [hz.L₂_le, hz.M₂_le]
        · rw [pos_k₁1]; exact hz.M₂_le

theorem L₂_le_pos {i : ℕ} (h1 : z.k₁ c₀ ≤ i) (hi : i < (z.word c₀ g₁ g₂ g₃ g₄).1) :
    z.L₂ ≤ (z.word c₀ g₁ g₂ g₃ g₄).2.1 i := by
  have hm := hz.m_eq (c₀ := c₀)
  rcases Nat.lt_or_ge i (z.m c₀ + 3) with h6 | h6
  · obtain rfl | rfl | rfl | rfl | rfl | rfl :
        i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 ∨ i = z.k₁ c₀ + 2 ∨ i = z.m c₀ ∨ i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by
      omega
    · rw [pos_k₁]
    · rw [pos_k₁1]; exact hz.L₂_le
    · rw [pos_k₁2]; exact hz.L₂_le.trans hz.M₂_le
    · rw [pos_m]; linarith [hz.L₂_le, hz.M₂_le, hz.R₂_le]
    · rw [pos_m1]; linarith [hz.L₂_le, hz.M₂_le, hz.R₂_le, hz.L₁_le]
    · rw [pos_m2]; linarith [hz.L₂_le, hz.M₂_le, hz.R₂_le, hz.L₁_le, hz.M₁_le]
  · linarith [hz.R₁_lt_pos hc₀ h6 hi, hz.L₂_le, hz.M₂_le, hz.R₂_le, hz.L₁_le, hz.M₁_le]

/-! ### The datum of the word -/

/-- **Left of the second base the datum is the original one at the preimage.** -/
theorem fn_zone₀ {x : ℝ} (hx : x < z.a₂) : (z.word c₀ g₁ g₂ g₃ g₄).fn (z.T x) = c₀.fn x := by
  have hm := hz.m_eq (c₀ := c₀)
  set t := c₀.index x with ht
  have htk : t ≤ z.k₁ c₀ := by
    by_contra h
    have hkN : z.k₁ c₀ < c₀.1 := lt_of_lt_of_le (not_le.1 h) (c₀.index_le x)
    have := (BoundaryWord.lt_index_iff hc₀ hkN).1 (not_le.1 h)
    have := (lt_k₁_iff hc₀ hkN).2 (this.trans hx)
    omega
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index (z.T x) = t := by
    refine BoundaryWord.index_eq_of_iff (htk.trans (by rw [word_fst]; omega)) fun i hi => ?_
    rcases Nat.lt_or_ge i (z.k₁ c₀) with hik | hik
    · have hiN : i < c₀.1 := lt_of_lt_of_le hik (card_filter_le_range _)
      rw [pos_of_lt hik, (hz.mono₀.lt_iff_lt ((lt_k₁_iff hc₀ hiN).1 hik) hx), BoundaryWord.lt_index_iff hc₀ hiN]
    · exact iff_of_false (not_lt.2 ((hz.T₀_lt x hx).le.trans (hz.L₂_le_pos hc₀ hik hi))) (by omega)
  unfold BoundaryWord.fn
  rw [hidx, ht_of_le htk]

/-- **Right of the first base the datum is the original one at the preimage.** -/
theorem fn_zone₂ {x : ℝ} (hx : z.b₁ < x) : (z.word c₀ g₁ g₂ g₃ g₄).fn (z.T x) = c₀.fn x := by
  set t := c₀.index x with ht
  have h4N := k₄_le (z := z) (c₀ := c₀)
  have htN : t ≤ c₀.1 := c₀.index_le x
  have hk4t : z.k₄ c₀ ≤ t := by
    by_contra h
    have hN : t < c₀.1 := by omega
    have h1 := (lt_k₄_iff hc₀ hN).1 (not_le.1 h)
    have h2 := (BoundaryWord.lt_index_iff hc₀ hN).2 (lt_of_le_of_lt h1 hx)
    omega
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index (z.T x) = z.m c₀ + 3 + (t - z.k₄ c₀) := by
    refine BoundaryWord.index_eq_of_iff (by rw [word_fst]; omega) fun i hi => ?_
    rcases Nat.lt_or_ge i (z.m c₀ + 3) with h6 | h6
    · refine iff_of_true ?_ (by omega)
      have hle : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i ≤ z.R₁ := by
        rcases Nat.lt_or_ge i (z.m c₀ + 1) with hi1 | hi1
        · linarith [hz.pos_le_L₁ hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
            hz.L₁_le, hz.M₁_le]
        · obtain rfl | rfl : i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by omega
          · rw [pos_m1]; exact hz.M₁_le
          · rw [pos_m2]
      exact lt_of_le_of_lt hle (hz.lt_T₂ x hx)
    · obtain ⟨hmem, hN⟩ := right_mem hc₀ h6 hi
      rw [pos_right h6, hz.mono₂.lt_iff_lt hmem hx, ← BoundaryWord.lt_index_iff hc₀ hN, ← ht]
      omega
  have e : z.m c₀ + 3 + (t - z.k₄ c₀) - (z.m c₀ + 3) + z.k₄ c₀ = t := by omega
  show (z.word c₀ g₁ g₂ g₃ g₄).2.2 ((z.word c₀ g₁ g₂ g₃ g₄).index (z.T x)) = c₀.2.2 t
  rw [hidx, ht_right (j := z.m c₀ + 3 + (t - z.k₄ c₀)) (by omega), e]

/-- The index of a point strictly between two consecutive positions. -/
theorem index_eq_of_btw {t : ℕ} {w : ℝ} (ht : t < (z.word c₀ g₁ g₂ g₃ g₄).1)
    (hlo : ∀ i < t, (z.word c₀ g₁ g₂ g₃ g₄).2.1 i < w) (hhi : w < (z.word c₀ g₁ g₂ g₃ g₄).2.1 t) :
    (z.word c₀ g₁ g₂ g₃ g₄).index w = t := by
  refine BoundaryWord.index_eq_of_iff ht.le fun i hi => ⟨fun h => ?_, fun h => hlo i h⟩
  by_contra hti
  exact absurd ((hz.word_isSorted hc₀ t i (not_lt.1 hti) hi).trans_lt h) (not_lt.2 hhi.le)

/-- The second prefix's left side `(L₂, M₂)` carries `g₁`. -/
theorem fn_side₁ {w : ℝ} (h1 : z.L₂ < w) (h2 : w < z.M₂) : (z.word c₀ g₁ g₂ g₃ g₄).fn w = g₁ := by
  have hm := hz.m_eq (c₀ := c₀)
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index w = z.k₁ c₀ + 1 := by
    refine hz.index_eq_of_btw hc₀ (by rw [word_fst]; omega) (fun i hi => ?_) (by rw [pos_k₁1]; exact h2)
    rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
    · exact (hz.pos_lt_L₂ hc₀ hi0).trans h1
    · obtain rfl : i = z.k₁ c₀ := by omega
      rw [pos_k₁]; exact h1
  unfold BoundaryWord.fn
  rw [hidx, ht_k₁1]

/-- The second prefix's right side `(M₂, R₂)` carries `g₂`. -/
theorem fn_side₂ {w : ℝ} (h1 : z.M₂ < w) (h2 : w < z.R₂) : (z.word c₀ g₁ g₂ g₃ g₄).fn w = g₂ := by
  have hm := hz.m_eq (c₀ := c₀)
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index w = z.k₁ c₀ + 2 := by
    refine hz.index_eq_of_btw hc₀ (by rw [word_fst]; omega) (fun i hi => ?_) (by rw [pos_k₁2]; exact h2)
    rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
    · linarith [hz.pos_lt_L₂ hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hi0, hz.L₂_le]
    · obtain rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 := by omega
      · rw [pos_k₁]; linarith [hz.L₂_le]
      · rw [pos_k₁1]; exact h1
  unfold BoundaryWord.fn
  rw [hidx, ht_k₁2]

/-- The first prefix's left side `(L₁, M₁)` carries `g₃`. -/
theorem fn_side₃ {w : ℝ} (h1 : z.L₁ < w) (h2 : w < z.M₁) : (z.word c₀ g₁ g₂ g₃ g₄).fn w = g₃ := by
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index w = z.m c₀ + 1 := by
    refine hz.index_eq_of_btw hc₀ (by rw [word_fst]; omega) (fun i hi => ?_) (by rw [pos_m1]; exact h2)
    exact lt_of_le_of_lt (hz.pos_le_L₁ hc₀ (by omega)) h1
  unfold BoundaryWord.fn
  rw [hidx, ht_m1]

/-- The first prefix's right side `(M₁, R₁)` carries `g₄`. -/
theorem fn_side₄ {w : ℝ} (h1 : z.M₁ < w) (h2 : w < z.R₁) : (z.word c₀ g₁ g₂ g₃ g₄).fn w = g₄ := by
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index w = z.m c₀ + 2 := by
    refine hz.index_eq_of_btw hc₀ (by rw [word_fst]; omega) (fun i hi => ?_) (by rw [pos_m2]; exact h2)
    rcases Nat.lt_or_ge i (z.m c₀ + 1) with hi1 | hi1
    · linarith [hz.pos_le_L₁ hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
        hz.L₁_le]
    · obtain rfl : i = z.m c₀ + 1 := by omega
      rw [pos_m1]; exact h1
  unfold BoundaryWord.fn
  rw [hidx, ht_m2]

end Order

/-- **The positions of the touching word**: each is one of `L₂, M₂, R₂, L₁, M₁, R₁`, or the chart point `T y` of an
original jump `y` of one of the two untouched zones. -/
theorem pos_cases (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) {i : ℕ} (hi : i < (z.word c₀ g₁ g₂ g₃ g₄).1) :
    (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.L₂ ∨ (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.M₂ ∨
      (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.R₂ ∨ (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.L₁ ∨
      (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.M₁ ∨ (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.R₁ ∨
      ∃ j < c₀.1, (c₀.2.1 j < z.a₂ ∨ z.b₁ < c₀.2.1 j) ∧ (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.T (c₀.2.1 j) := by
  have hm := hz.m_eq (c₀ := c₀)
  rcases Nat.lt_or_ge i (z.k₁ c₀) with h0 | h0
  · have hiN : i < c₀.1 := lt_of_lt_of_le h0 (card_filter_le_range _)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨i, hiN, Or.inl ((lt_k₁_iff hc₀ hiN).1 h0), pos_of_lt h0⟩)))))
  rcases Nat.lt_or_ge i (z.m c₀ + 3) with h6 | h6
  · obtain rfl | rfl | rfl | rfl | rfl | rfl :
        i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 ∨ i = z.k₁ c₀ + 2 ∨ i = z.m c₀ ∨ i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by
      omega
    · exact Or.inl pos_k₁
    · exact Or.inr (Or.inl pos_k₁1)
    · exact Or.inr (Or.inr (Or.inl pos_k₁2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl pos_m)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl pos_m1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl pos_m2)))))
  · obtain ⟨hmem, hN⟩ := right_mem hc₀ h6 hi
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hN, Or.inr hmem, pos_right h6⟩)))))

end GoodT

end RetTouch

end RLC

end InteractingSLE
