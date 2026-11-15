/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma78MeanWord
import InteractingSLE.Spec.Sec4.ZeroMarksAvoid

/-!
# The boundary word of a disjoint pair (combinatorics)

Packet PROVE-LEMMA76G (proof of Lemma 7.6, pp. 268–269). In the retained chart of a disjoint pair the real line splits
into five zones: the untouched original boundary left of the second prefix's real base `[a₂, b₂]`, the two sides of
the second prefix (chart interval `[L₂, R₂]`, tip at `M₂ = 0`), the untouched boundary between the bases, the two sides
of the first prefix (`[L₁, R₁]`, tip `M₁`), and the untouched boundary right of the first base `[a₁, b₁]`. The word is
built from an original sorted word `c₀` and a boundary correspondence `T` (the chart image of untouched real points):

* positions `T(p_i)` for the original jumps `p_i < a₂`, then `L₂, M₂, R₂`, then `T(p_i)` for `b₂ < p_i < a₁`, then
  `L₁, M₁, R₁`, then `T(p_i)` for `p_i > b₁`;
* heights: the original ones on the untouched zones, `g₁, g₂` on `(L₂, M₂)`, `(M₂, R₂)` and `g₃, g₄` on `(L₁, M₁)`,
  `(M₁, R₁)`.

This file is pure combinatorics (`ZW`, `ZW.word`); under the order hypotheses `ZW.Good` the word is sorted and its
datum is the original datum at `T⁻¹(w)` on the untouched zones and the side heights on the four sides.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace InteractingSLE

namespace Sec7

namespace Lemma76G

open Restart

/-- The number of original jumps strictly left of `A`. -/
def cntLt (c₀ : BoundaryWord) (A : ℝ) : ℕ := ((Finset.range c₀.1).filter fun i => c₀.2.1 i < A).card

/-- The number of original jumps at most `A`. -/
def cntLe (c₀ : BoundaryWord) (A : ℝ) : ℕ := ((Finset.range c₀.1).filter fun i => c₀.2.1 i ≤ A).card

/-- The zone data of a disjoint pair: the boundary correspondence `T`, the real bases and the six chart points. -/
structure ZW where
  /-- The chart image of untouched real points. -/
  T : ℝ → ℝ
  /-- The left end of the second base. -/
  a₂ : ℝ
  /-- The right end of the second base. -/
  b₂ : ℝ
  /-- The left end of the first base. -/
  a₁ : ℝ
  /-- The right end of the first base. -/
  b₁ : ℝ
  /-- The chart image of `a₂`. -/
  L₂ : ℝ
  /-- The second tip. -/
  M₂ : ℝ
  /-- The chart image of `b₂`. -/
  R₂ : ℝ
  /-- The chart image of `a₁`. -/
  L₁ : ℝ
  /-- The first tip. -/
  M₁ : ℝ
  /-- The chart image of `b₁`. -/
  R₁ : ℝ

namespace ZW

variable (z : ZW) (c₀ : BoundaryWord)

/-- The first block end. -/
def k₁ : ℕ := cntLt c₀ z.a₂
/-- The start of the middle block in `c₀`. -/
def k₂ : ℕ := cntLe c₀ z.b₂
/-- The end of the middle block in `c₀`. -/
def k₃ : ℕ := cntLt c₀ z.a₁
/-- The start of the right block in `c₀`. -/
def k₄ : ℕ := cntLe c₀ z.b₁
/-- The index of `L₁` in the word. -/
def m : ℕ := z.k₁ c₀ + 3 + (z.k₃ c₀ - z.k₂ c₀)

/-- **The boundary word of a disjoint pair.** -/
def word (g₁ g₂ g₃ g₄ : ℝ) : BoundaryWord :=
  (z.m c₀ + 3 + (c₀.1 - z.k₄ c₀),
    fun i => if i < z.k₁ c₀ then z.T (c₀.2.1 i) else if i = z.k₁ c₀ then z.L₂ else if i = z.k₁ c₀ + 1 then z.M₂
      else if i = z.k₁ c₀ + 2 then z.R₂ else if i < z.m c₀ then z.T (c₀.2.1 (i - (z.k₁ c₀ + 3) + z.k₂ c₀))
      else if i = z.m c₀ then z.L₁ else if i = z.m c₀ + 1 then z.M₁ else if i = z.m c₀ + 2 then z.R₁
      else z.T (c₀.2.1 (i - (z.m c₀ + 3) + z.k₄ c₀)),
    fun j => if j ≤ z.k₁ c₀ then c₀.2.2 j else if j = z.k₁ c₀ + 1 then g₁ else if j = z.k₁ c₀ + 2 then g₂
      else if j ≤ z.m c₀ then c₀.2.2 (j - (z.k₁ c₀ + 3) + z.k₂ c₀) else if j = z.m c₀ + 1 then g₃
      else if j = z.m c₀ + 2 then g₄ else c₀.2.2 (j - (z.m c₀ + 3) + z.k₄ c₀))

/-- The order hypotheses on the zone data. -/
structure Good : Prop where
  a₂_le_b₂ : z.a₂ ≤ z.b₂
  b₂_lt_a₁ : z.b₂ < z.a₁
  a₁_le_b₁ : z.a₁ ≤ z.b₁
  mono₀ : StrictMonoOn z.T (Iio z.a₂)
  mono₁ : StrictMonoOn z.T (Ioo z.b₂ z.a₁)
  mono₂ : StrictMonoOn z.T (Ioi z.b₁)
  T₀_lt : ∀ x < z.a₂, z.T x < z.L₂
  L₂_le : z.L₂ ≤ z.M₂
  M₂_le : z.M₂ ≤ z.R₂
  lt_T₁ : ∀ x ∈ Ioo z.b₂ z.a₁, z.R₂ < z.T x
  T₁_lt : ∀ x ∈ Ioo z.b₂ z.a₁, z.T x < z.L₁
  L₁_le : z.L₁ ≤ z.M₁
  M₁_le : z.M₁ ≤ z.R₁
  lt_T₂ : ∀ x, z.b₁ < x → z.R₁ < z.T x

variable {z c₀} {g₁ g₂ g₃ g₄ : ℝ}

theorem word_fst : (z.word c₀ g₁ g₂ g₃ g₄).1 = z.m c₀ + 3 + (c₀.1 - z.k₄ c₀) := rfl

theorem cnt_le (P : ℕ → Prop) [DecidablePred P] : ((Finset.range c₀.1).filter P).card ≤ c₀.1 :=
  card_filter_le_range P

/-! ### Positions and heights -/

theorem pos_of_lt {i : ℕ} (hi : i < z.k₁ c₀) : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.T (c₀.2.1 i) := by
  simp only [word, m, hi, ↓reduceIte]

theorem pos_k₁ : (z.word c₀ g₁ g₂ g₃ g₄).2.1 (z.k₁ c₀) = z.L₂ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem pos_k₁1 : (z.word c₀ g₁ g₂ g₃ g₄).2.1 (z.k₁ c₀ + 1) = z.M₂ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem pos_k₁2 : (z.word c₀ g₁ g₂ g₃ g₄).2.1 (z.k₁ c₀ + 2) = z.R₂ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem pos_mid {i : ℕ} (h1 : z.k₁ c₀ + 3 ≤ i) (h2 : i < z.m c₀) :
    (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.T (c₀.2.1 (i - (z.k₁ c₀ + 3) + z.k₂ c₀)) := by
  simp only [m] at h2
  have a1 : ¬ i < z.k₁ c₀ := by omega
  have a2 : i ≠ z.k₁ c₀ := by omega
  have a3 : i ≠ z.k₁ c₀ + 1 := by omega
  have a4 : i ≠ z.k₁ c₀ + 2 := by omega
  simp only [word, m, a1, a2, a3, a4, h2, ↓reduceIte]

theorem pos_m : (z.word c₀ g₁ g₂ g₃ g₄).2.1 (z.m c₀) = z.L₁ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem pos_m1 : (z.word c₀ g₁ g₂ g₃ g₄).2.1 (z.m c₀ + 1) = z.M₁ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem pos_m2 : (z.word c₀ g₁ g₂ g₃ g₄).2.1 (z.m c₀ + 2) = z.R₁ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem pos_right {i : ℕ} (h1 : z.m c₀ + 3 ≤ i) :
    (z.word c₀ g₁ g₂ g₃ g₄).2.1 i = z.T (c₀.2.1 (i - (z.m c₀ + 3) + z.k₄ c₀)) := by
  simp only [m] at h1
  have a1 : ¬ i < z.k₁ c₀ := by omega
  have a2 : i ≠ z.k₁ c₀ := by omega
  have a3 : i ≠ z.k₁ c₀ + 1 := by omega
  have a4 : i ≠ z.k₁ c₀ + 2 := by omega
  have a5 : ¬ i < z.k₁ c₀ + 3 + (z.k₃ c₀ - z.k₂ c₀) := by omega
  have a6 : i ≠ z.k₁ c₀ + 3 + (z.k₃ c₀ - z.k₂ c₀) := by omega
  have a7 : i ≠ z.k₁ c₀ + 3 + (z.k₃ c₀ - z.k₂ c₀) + 1 := by omega
  have a8 : i ≠ z.k₁ c₀ + 3 + (z.k₃ c₀ - z.k₂ c₀) + 2 := by omega
  simp only [word, m, a1, a2, a3, a4, a5, a6, a7, a8, ↓reduceIte]

theorem ht_of_le {j : ℕ} (hj : j ≤ z.k₁ c₀) : (z.word c₀ g₁ g₂ g₃ g₄).2.2 j = c₀.2.2 j := by
  simp only [word, m, hj, ↓reduceIte]

theorem ht_k₁1 : (z.word c₀ g₁ g₂ g₃ g₄).2.2 (z.k₁ c₀ + 1) = g₁ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem ht_k₁2 : (z.word c₀ g₁ g₂ g₃ g₄).2.2 (z.k₁ c₀ + 2) = g₂ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem ht_mid {j : ℕ} (h1 : z.k₁ c₀ + 3 ≤ j) (h2 : j ≤ z.m c₀) :
    (z.word c₀ g₁ g₂ g₃ g₄).2.2 j = c₀.2.2 (j - (z.k₁ c₀ + 3) + z.k₂ c₀) := by
  simp only [m] at h2
  have a1 : ¬ j ≤ z.k₁ c₀ := by omega
  have a3 : j ≠ z.k₁ c₀ + 1 := by omega
  have a4 : j ≠ z.k₁ c₀ + 2 := by omega
  simp only [word, m, a1, a3, a4, h2, ↓reduceIte]

theorem ht_m1 : (z.word c₀ g₁ g₂ g₃ g₄).2.2 (z.m c₀ + 1) = g₃ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem ht_m2 : (z.word c₀ g₁ g₂ g₃ g₄).2.2 (z.m c₀ + 2) = g₄ := by
  simp only [word, m]; split_ifs <;> first | rfl | omega

theorem ht_right {j : ℕ} (h1 : z.m c₀ + 3 ≤ j) :
    (z.word c₀ g₁ g₂ g₃ g₄).2.2 j = c₀.2.2 (j - (z.m c₀ + 3) + z.k₄ c₀) := by
  simp only [m] at h1
  have a1 : ¬ j ≤ z.k₁ c₀ := by omega
  have a3 : j ≠ z.k₁ c₀ + 1 := by omega
  have a4 : j ≠ z.k₁ c₀ + 2 := by omega
  have a5 : ¬ j ≤ z.k₁ c₀ + 3 + (z.k₃ c₀ - z.k₂ c₀) := by omega
  have a6 : j ≠ z.k₁ c₀ + 3 + (z.k₃ c₀ - z.k₂ c₀) + 1 := by omega
  have a7 : j ≠ z.k₁ c₀ + 3 + (z.k₃ c₀ - z.k₂ c₀) + 2 := by omega
  simp only [word, m, a1, a3, a4, a5, a6, a7, ↓reduceIte]

/-! ### Counting -/

section Count

variable (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
include hc₀

theorem lt_k₁_iff {i : ℕ} (hi : i < c₀.1) : i < z.k₁ c₀ ↔ c₀.2.1 i < z.a₂ :=
  lt_card_filter_iff hc₀ (P := fun y => y < z.a₂) (fun _ _ h1 h2 => lt_of_le_of_lt h1 h2) hi

theorem lt_k₂_iff {i : ℕ} (hi : i < c₀.1) : i < z.k₂ c₀ ↔ c₀.2.1 i ≤ z.b₂ :=
  lt_card_filter_iff hc₀ (P := fun y => y ≤ z.b₂) (fun _ _ h1 h2 => h1.trans h2) hi

theorem lt_k₃_iff {i : ℕ} (hi : i < c₀.1) : i < z.k₃ c₀ ↔ c₀.2.1 i < z.a₁ :=
  lt_card_filter_iff hc₀ (P := fun y => y < z.a₁) (fun _ _ h1 h2 => lt_of_le_of_lt h1 h2) hi

theorem lt_k₄_iff {i : ℕ} (hi : i < c₀.1) : i < z.k₄ c₀ ↔ c₀.2.1 i ≤ z.b₁ :=
  lt_card_filter_iff hc₀ (P := fun y => y ≤ z.b₁) (fun _ _ h1 h2 => h1.trans h2) hi

end Count

theorem k₄_le : z.k₄ c₀ ≤ c₀.1 := card_filter_le_range _

theorem k₁_le_k₂ (hz : z.Good) : z.k₁ c₀ ≤ z.k₂ c₀ := by
  unfold k₁ k₂ cntLt cntLe
  exact Finset.card_le_card fun i => by
    simp only [Finset.mem_filter]
    exact fun ⟨h1, h2⟩ => ⟨h1, h2.le.trans hz.a₂_le_b₂⟩

theorem k₂_le_k₃ (hz : z.Good) : z.k₂ c₀ ≤ z.k₃ c₀ := by
  unfold k₂ k₃ cntLt cntLe
  exact Finset.card_le_card fun i => by
    simp only [Finset.mem_filter]
    exact fun ⟨h1, h2⟩ => ⟨h1, lt_of_le_of_lt h2 hz.b₂_lt_a₁⟩

theorem k₃_le_k₄ (hz : z.Good) : z.k₃ c₀ ≤ z.k₄ c₀ := by
  unfold k₃ k₄ cntLt cntLe
  exact Finset.card_le_card fun i => by
    simp only [Finset.mem_filter]
    exact fun ⟨h1, h2⟩ => ⟨h1, h2.le.trans hz.a₁_le_b₁⟩

/-! ### The order of the positions -/

section Order

variable (hz : z.Good) (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
include hz hc₀

theorem pos_lt_L₂ {i : ℕ} (hi : i < z.k₁ c₀) : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i < z.L₂ := by
  have hiN : i < c₀.1 := lt_of_lt_of_le hi (card_filter_le_range _)
  rw [pos_of_lt hi]
  exact hz.T₀_lt _ ((lt_k₁_iff hc₀ hiN).1 hi)

theorem mid_mem {i : ℕ} (h1 : z.k₁ c₀ + 3 ≤ i) (h2 : i < z.m c₀) :
    c₀.2.1 (i - (z.k₁ c₀ + 3) + z.k₂ c₀) ∈ Ioo z.b₂ z.a₁ ∧ i - (z.k₁ c₀ + 3) + z.k₂ c₀ < c₀.1 := by
  have h23 := k₂_le_k₃ (c₀ := c₀) hz
  have h3N : z.k₃ c₀ ≤ c₀.1 := card_filter_le_range _
  simp only [m] at h2
  have hN : i - (z.k₁ c₀ + 3) + z.k₂ c₀ < c₀.1 := by omega
  refine ⟨⟨not_le.1 fun h => ?_, (lt_k₃_iff hc₀ hN).1 (by omega)⟩, hN⟩
  have := (lt_k₂_iff hc₀ hN).2 h
  omega

theorem pos_mid_mem {i : ℕ} (h1 : z.k₁ c₀ + 3 ≤ i) (h2 : i < z.m c₀) :
    z.R₂ < (z.word c₀ g₁ g₂ g₃ g₄).2.1 i ∧ (z.word c₀ g₁ g₂ g₃ g₄).2.1 i < z.L₁ := by
  rw [pos_mid h1 h2]
  exact ⟨hz.lt_T₁ _ (mid_mem hz hc₀ h1 h2).1, hz.T₁_lt _ (mid_mem hz hc₀ h1 h2).1⟩

omit hz in
theorem right_mem {i : ℕ} (h1 : z.m c₀ + 3 ≤ i) (hi : i < (z.word c₀ g₁ g₂ g₃ g₄).1) :
    z.b₁ < c₀.2.1 (i - (z.m c₀ + 3) + z.k₄ c₀) ∧ i - (z.m c₀ + 3) + z.k₄ c₀ < c₀.1 := by
  rw [word_fst] at hi
  have h4N := k₄_le (z := z) (c₀ := c₀)
  have hN : i - (z.m c₀ + 3) + z.k₄ c₀ < c₀.1 := by omega
  refine ⟨not_le.1 fun h => ?_, hN⟩
  have := (lt_k₄_iff hc₀ hN).2 h
  omega

theorem R₁_lt_pos {i : ℕ} (h1 : z.m c₀ + 3 ≤ i) (hi : i < (z.word c₀ g₁ g₂ g₃ g₄).1) :
    z.R₁ < (z.word c₀ g₁ g₂ g₃ g₄).2.1 i := by
  rw [pos_right h1]
  exact hz.lt_T₂ _ (right_mem hc₀ h1 hi).1

/-- The positions below `m` are at most `L₁`; from `m + 3` on they exceed `R₁`. -/
theorem pos_le_L₁ {i : ℕ} (hi : i ≤ z.m c₀) : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i ≤ z.L₁ := by
  have hRL : z.R₂ < z.L₁ := by
    obtain ⟨x, hx⟩ : (Ioo z.b₂ z.a₁).Nonempty := nonempty_Ioo.2 hz.b₂_lt_a₁
    exact (hz.lt_T₁ x hx).trans (hz.T₁_lt x hx)
  rcases hi.lt_or_eq with hi | rfl
  · rcases Nat.lt_or_ge i (z.k₁ c₀) with h1 | h1
    · linarith [pos_lt_L₂ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) h1, hz.L₂_le, hz.M₂_le]
    rcases Nat.lt_or_ge i (z.k₁ c₀ + 3) with h3 | h3
    · obtain rfl | rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 ∨ i = z.k₁ c₀ + 2 := by omega
      · rw [pos_k₁]; linarith [hz.L₂_le, hz.M₂_le]
      · rw [pos_k₁1]; linarith [hz.M₂_le]
      · rw [pos_k₁2]; exact hRL.le
    · exact (pos_mid_mem hz hc₀ h3 hi).2.le
  · rw [pos_m]

/-- **The word is sorted.** -/
theorem word_isSorted : (z.word c₀ g₁ g₂ g₃ g₄).IsSorted := by
  intro i j hij hjn
  rcases hij.lt_or_eq with hlt | rfl
  swap
  · exact le_rfl
  have hin : i < (z.word c₀ g₁ g₂ g₃ g₄).1 := lt_trans hlt hjn
  have hk12 := k₁_le_k₂ (c₀ := c₀) hz
  have hm3 : z.k₁ c₀ + 3 ≤ z.m c₀ := by unfold m; omega
  -- `j` beyond `m + 2`
  rcases Nat.lt_or_ge j (z.m c₀ + 3) with hj3 | hj3
  swap
  · rcases Nat.lt_or_ge i (z.m c₀ + 3) with hi3 | hi3
    · have hjR := R₁_lt_pos hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hj3 hjn
      rcases Nat.lt_or_ge i (z.m c₀ + 1) with hi1 | hi1
      · linarith [pos_le_L₁ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
          hz.L₁_le, hz.M₁_le]
      · obtain rfl | rfl : i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by omega
        · rw [pos_m1]; linarith [hz.M₁_le]
        · rw [pos_m2]; exact hjR.le
    · obtain ⟨hmi, hiN⟩ := right_mem hc₀ hi3 hin
      obtain ⟨hmj, hjN⟩ := right_mem hc₀ hj3 hjn
      rw [pos_right hi3, pos_right hj3]
      exact (hz.mono₂ hmi hmj (hc₀ hiN hjN (by omega))).le
  -- `j ≤ m + 2`
  rcases Nat.lt_or_ge j (z.m c₀ + 1) with hj1 | hj1
  swap
  · have hiL : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i ≤ (z.word c₀ g₁ g₂ g₃ g₄).2.1 (z.m c₀ + 1) := by
      rw [pos_m1]
      rcases Nat.lt_or_ge i (z.m c₀ + 1) with hi1 | hi1
      · linarith [pos_le_L₁ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
          hz.L₁_le]
      · obtain rfl : i = z.m c₀ + 1 := by omega
        rw [pos_m1]
    obtain rfl | rfl : j = z.m c₀ + 1 ∨ j = z.m c₀ + 2 := by omega
    · exact hiL
    · rw [pos_m2]; rw [pos_m1] at hiL; linarith [hz.M₁_le]
  rcases (show j ≤ z.m c₀ by omega).lt_or_eq with hjm | rfl
  swap
  · rw [pos_m]; exact pos_le_L₁ hz hc₀ (show i ≤ z.m c₀ by omega)
  -- `j < m`
  rcases Nat.lt_or_ge j (z.k₁ c₀ + 3) with hjk | hjk
  · rcases Nat.lt_or_ge j (z.k₁ c₀) with hj0 | hj0
    · -- both in the left block
      have hjN : j < c₀.1 := lt_of_lt_of_le hj0 (card_filter_le_range _)
      have hiN : i < c₀.1 := lt_trans hlt hjN
      rw [pos_of_lt (lt_trans hlt hj0), pos_of_lt hj0]
      exact (hz.mono₀ ((lt_k₁_iff hc₀ hiN).1 (lt_trans hlt hj0)) ((lt_k₁_iff hc₀ hjN).1 hj0)
        (hc₀ hiN hjN hlt)).le
    · obtain rfl | rfl | rfl : j = z.k₁ c₀ ∨ j = z.k₁ c₀ + 1 ∨ j = z.k₁ c₀ + 2 := by omega
      · rw [pos_k₁]
        rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
        · exact (pos_lt_L₂ hz hc₀ hi0).le
        · exfalso; omega
      · rw [pos_k₁1]
        rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
        · linarith [pos_lt_L₂ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hi0, hz.L₂_le]
        · obtain rfl : i = z.k₁ c₀ := by omega
          rw [pos_k₁]; exact hz.L₂_le
      · rw [pos_k₁2]
        rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
        · linarith [pos_lt_L₂ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hi0, hz.L₂_le, hz.M₂_le]
        · obtain rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 := by omega
          · rw [pos_k₁]; linarith [hz.L₂_le, hz.M₂_le]
          · rw [pos_k₁1]; exact hz.M₂_le
  · -- `j` in the middle block
    have hjR := (pos_mid_mem hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hjk hjm).1
    rcases Nat.lt_or_ge i (z.k₁ c₀ + 3) with hik | hik
    · have hiR : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i ≤ z.R₂ := by
        rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
        · linarith [pos_lt_L₂ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hi0, hz.L₂_le, hz.M₂_le]
        · obtain rfl | rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 ∨ i = z.k₁ c₀ + 2 := by omega
          · rw [pos_k₁]; linarith [hz.L₂_le, hz.M₂_le]
          · rw [pos_k₁1]; exact hz.M₂_le
          · rw [pos_k₁2]
      exact (hiR.trans hjR.le)
    · obtain ⟨hmi, hiN⟩ := mid_mem hz hc₀ hik (lt_trans hlt hjm)
      obtain ⟨hmj, hjN⟩ := mid_mem hz hc₀ hjk hjm
      rw [pos_mid hik (lt_trans hlt hjm), pos_mid hjk hjm]
      exact (hz.mono₁ hmi hmj (hc₀ hiN hjN (by omega))).le

end Order

/-! ### The datum of the word -/

section Datum

variable (hz : z.Good) (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1))
include hz hc₀

theorem L₂_le_pos {i : ℕ} (h1 : z.k₁ c₀ ≤ i) (hi : i < (z.word c₀ g₁ g₂ g₃ g₄).1) :
    z.L₂ ≤ (z.word c₀ g₁ g₂ g₃ g₄).2.1 i := by
  have hm3 : z.k₁ c₀ + 3 ≤ z.m c₀ := by unfold m; omega
  have hRL : z.R₂ < z.L₁ := by
    obtain ⟨x, hx⟩ : (Ioo z.b₂ z.a₁).Nonempty := nonempty_Ioo.2 hz.b₂_lt_a₁
    exact (hz.lt_T₁ x hx).trans (hz.T₁_lt x hx)
  rcases Nat.lt_or_ge i (z.k₁ c₀ + 3) with h3 | h3
  · obtain rfl | rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 ∨ i = z.k₁ c₀ + 2 := by omega
    · rw [pos_k₁]
    · rw [pos_k₁1]; exact hz.L₂_le
    · rw [pos_k₁2]; exact hz.L₂_le.trans hz.M₂_le
  rcases Nat.lt_or_ge i (z.m c₀) with hm | hm
  · linarith [(pos_mid_mem hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) h3 hm).1, hz.L₂_le, hz.M₂_le]
  rcases Nat.lt_or_ge i (z.m c₀ + 3) with h6 | h6
  · obtain rfl | rfl | rfl : i = z.m c₀ ∨ i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by omega
    · rw [pos_m]; linarith [hz.L₂_le, hz.M₂_le]
    · rw [pos_m1]; linarith [hz.L₂_le, hz.M₂_le, hz.L₁_le]
    · rw [pos_m2]; linarith [hz.L₂_le, hz.M₂_le, hz.L₁_le, hz.M₁_le]
  · linarith [R₁_lt_pos hz hc₀ h6 hi, hz.L₂_le, hz.M₂_le, hz.L₁_le, hz.M₁_le]

/-- **Left of the second base the datum is the original one at the preimage.** -/
theorem fn_zone₀ {x : ℝ} (hx : x < z.a₂) : (z.word c₀ g₁ g₂ g₃ g₄).fn (z.T x) = c₀.fn x := by
  set t := c₀.index x with ht
  have htk : t ≤ z.k₁ c₀ := by
    by_contra h
    have hkN : z.k₁ c₀ < c₀.1 := lt_of_lt_of_le (not_le.1 h) (c₀.index_le x)
    have := (BoundaryWord.lt_index_iff hc₀ hkN).1 (not_le.1 h)
    have := (lt_k₁_iff hc₀ hkN).2 (this.trans hx)
    omega
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index (z.T x) = t := by
    refine BoundaryWord.index_eq_of_iff (htk.trans (by rw [word_fst]; unfold m; omega)) fun i hi => ?_
    rcases Nat.lt_or_ge i (z.k₁ c₀) with hik | hik
    · have hiN : i < c₀.1 := lt_of_lt_of_le hik (card_filter_le_range _)
      rw [pos_of_lt hik, (hz.mono₀.lt_iff_lt ((lt_k₁_iff hc₀ hiN).1 hik) hx), BoundaryWord.lt_index_iff hc₀ hiN]
    · exact iff_of_false (not_lt.2 ((hz.T₀_lt x hx).le.trans (L₂_le_pos hz hc₀ hik hi))) (by omega)
  unfold BoundaryWord.fn
  rw [hidx, ht_of_le htk]

/-- **Between the bases the datum is the original one at the preimage.** -/
theorem fn_zone₁ {x : ℝ} (hx : x ∈ Ioo z.b₂ z.a₁) :
    (z.word c₀ g₁ g₂ g₃ g₄).fn (z.T x) = c₀.fn x := by
  set t := c₀.index x with ht
  have hk23 := k₂_le_k₃ (c₀ := c₀) hz
  have h3N : z.k₃ c₀ ≤ c₀.1 := card_filter_le_range _
  have hk2t : z.k₂ c₀ ≤ t := by
    by_contra h
    have hN : t < c₀.1 := by omega
    have h1 := (lt_k₂_iff hc₀ hN).1 (not_le.1 h)
    have h2 := (BoundaryWord.lt_index_iff hc₀ hN).2 (lt_of_le_of_lt h1 hx.1)
    omega
  have htk3 : t ≤ z.k₃ c₀ := by
    by_contra h
    have hkN : z.k₃ c₀ < c₀.1 := lt_of_lt_of_le (not_le.1 h) (c₀.index_le x)
    have := (BoundaryWord.lt_index_iff hc₀ hkN).1 (not_le.1 h)
    have := (lt_k₃_iff hc₀ hkN).2 (this.trans hx.2)
    omega
  have hm : z.m c₀ = z.k₁ c₀ + 3 + (z.k₃ c₀ - z.k₂ c₀) := rfl
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index (z.T x) = z.k₁ c₀ + 3 + (t - z.k₂ c₀) := by
    refine BoundaryWord.index_eq_of_iff (by rw [word_fst]; omega) fun i hi => ?_
    rcases Nat.lt_or_ge i (z.k₁ c₀ + 3) with h3 | h3
    · refine iff_of_true ?_ (by omega)
      have hle : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i ≤ z.R₂ := by
        rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
        · linarith [pos_lt_L₂ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hi0, hz.L₂_le, hz.M₂_le]
        · obtain rfl | rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 ∨ i = z.k₁ c₀ + 2 := by omega
          · rw [pos_k₁]; linarith [hz.L₂_le, hz.M₂_le]
          · rw [pos_k₁1]; exact hz.M₂_le
          · rw [pos_k₁2]
      exact lt_of_le_of_lt hle (hz.lt_T₁ x hx)
    rcases Nat.lt_or_ge i (z.m c₀) with hmi | hmi
    · obtain ⟨hmem, hN⟩ := mid_mem hz hc₀ h3 hmi
      rw [pos_mid h3 hmi, hz.mono₁.lt_iff_lt hmem hx, ← BoundaryWord.lt_index_iff hc₀ hN, ← ht]
      omega
    · refine iff_of_false (not_lt.2 ?_) (by omega)
      rcases Nat.lt_or_ge i (z.m c₀ + 3) with h6 | h6
      · obtain rfl | rfl | rfl : i = z.m c₀ ∨ i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by omega
        · rw [pos_m]; exact (hz.T₁_lt x hx).le
        · rw [pos_m1]; linarith [hz.T₁_lt x hx, hz.L₁_le]
        · rw [pos_m2]; linarith [hz.T₁_lt x hx, hz.L₁_le, hz.M₁_le]
      · linarith [R₁_lt_pos hz hc₀ h6 hi, hz.T₁_lt x hx, hz.L₁_le, hz.M₁_le]
  have e : z.k₁ c₀ + 3 + (t - z.k₂ c₀) - (z.k₁ c₀ + 3) + z.k₂ c₀ = t := by omega
  show (z.word c₀ g₁ g₂ g₃ g₄).2.2 ((z.word c₀ g₁ g₂ g₃ g₄).index (z.T x)) = c₀.2.2 t
  rw [hidx, ht_mid (j := z.k₁ c₀ + 3 + (t - z.k₂ c₀)) (by omega) (by omega), e]

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
        · linarith [pos_le_L₁ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
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
  exact absurd ((word_isSorted hz hc₀ t i (not_lt.1 hti) hi).trans_lt h) (not_lt.2 hhi.le)

theorem fn_side₁ {w : ℝ} (h1 : z.L₂ < w) (h2 : w < z.M₂) : (z.word c₀ g₁ g₂ g₃ g₄).fn w = g₁ := by
  have hm3 : z.k₁ c₀ + 3 ≤ z.m c₀ := by unfold m; omega
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index w = z.k₁ c₀ + 1 := by
    refine index_eq_of_btw hz hc₀ (by rw [word_fst]; omega) (fun i hi => ?_) (by rw [pos_k₁1]; exact h2)
    rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
    · exact (pos_lt_L₂ hz hc₀ hi0).trans h1
    · obtain rfl : i = z.k₁ c₀ := by omega
      rw [pos_k₁]; exact h1
  unfold BoundaryWord.fn
  rw [hidx, ht_k₁1]

theorem fn_side₂ {w : ℝ} (h1 : z.M₂ < w) (h2 : w < z.R₂) : (z.word c₀ g₁ g₂ g₃ g₄).fn w = g₂ := by
  have hm3 : z.k₁ c₀ + 3 ≤ z.m c₀ := by unfold m; omega
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index w = z.k₁ c₀ + 2 := by
    refine index_eq_of_btw hz hc₀ (by rw [word_fst]; omega) (fun i hi => ?_) (by rw [pos_k₁2]; exact h2)
    rcases Nat.lt_or_ge i (z.k₁ c₀) with hi0 | hi0
    · linarith [pos_lt_L₂ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) hi0, hz.L₂_le]
    · obtain rfl | rfl : i = z.k₁ c₀ ∨ i = z.k₁ c₀ + 1 := by omega
      · rw [pos_k₁]; linarith [hz.L₂_le]
      · rw [pos_k₁1]; exact h1
  unfold BoundaryWord.fn
  rw [hidx, ht_k₁2]

theorem fn_side₃ {w : ℝ} (h1 : z.L₁ < w) (h2 : w < z.M₁) : (z.word c₀ g₁ g₂ g₃ g₄).fn w = g₃ := by
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index w = z.m c₀ + 1 := by
    refine index_eq_of_btw hz hc₀ (by rw [word_fst]; omega) (fun i hi => ?_) (by rw [pos_m1]; exact h2)
    exact lt_of_le_of_lt (pos_le_L₁ hz hc₀ (by omega)) h1
  unfold BoundaryWord.fn
  rw [hidx, ht_m1]

theorem fn_side₄ {w : ℝ} (h1 : z.M₁ < w) (h2 : w < z.R₁) : (z.word c₀ g₁ g₂ g₃ g₄).fn w = g₄ := by
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index w = z.m c₀ + 2 := by
    refine index_eq_of_btw hz hc₀ (by rw [word_fst]; omega) (fun i hi => ?_) (by rw [pos_m2]; exact h2)
    rcases Nat.lt_or_ge i (z.m c₀ + 1) with hi1 | hi1
    · linarith [pos_le_L₁ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
        hz.L₁_le]
    · obtain rfl : i = z.m c₀ + 1 := by omega
      rw [pos_m1]; exact h1
  unfold BoundaryWord.fn
  rw [hidx, ht_m2]

/-- No jump of the word lies strictly between `M₁` and `R₁`. -/
theorem notMem_jumps_side₄ {w : ℝ} (h1 : z.M₁ < w) (h2 : w < z.R₁) : w ∉ (z.word c₀ g₁ g₂ g₃ g₄).jumps := by
  intro hw
  obtain ⟨i, hi, hiw⟩ := BoundaryWord.mem_jumps.1 hw
  rcases Nat.lt_or_ge i (z.m c₀ + 1) with hi1 | hi1
  · linarith [pos_le_L₁ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
      hz.L₁_le]
  rcases Nat.lt_or_ge i (z.m c₀ + 3) with h6 | h6
  · obtain rfl | rfl : i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by omega
    · rw [pos_m1] at hiw; linarith
    · rw [pos_m2] at hiw; linarith
  · linarith [R₁_lt_pos hz hc₀ h6 hi]

/-- **The right limit of the datum at `R₁` is the original right limit at `b₁`** (the junction). -/
theorem rightLim_fn_R₁ {b : ℝ → ℝ} {J : Finset ℝ} (hb : ∀ y ∉ J, c₀.fn y = b y) :
    PiecewiseConstantBoundaryData.rightLim (z.word c₀ g₁ g₂ g₃ g₄).fn z.R₁ =
      PiecewiseConstantBoundaryData.rightLim b z.b₁ := by
  -- the common value `q_{k₄}`
  have h4N := k₄_le (z := z) (c₀ := c₀)
  -- right of `b₁` before the next original jump
  obtain ⟨ε, hε, hεJ⟩ : ∃ ε > 0, ∀ i < c₀.1, z.b₁ < c₀.2.1 i → z.b₁ + ε ≤ c₀.2.1 i := by
    by_cases hN : ∃ i < c₀.1, z.b₁ < c₀.2.1 i
    · obtain ⟨i₀, hi₀, hi₀b⟩ := hN
      set S := (Finset.range c₀.1).filter fun i => z.b₁ < c₀.2.1 i with hS
      have hSne : S.Nonempty := ⟨i₀, by simp [hS, hi₀, hi₀b]⟩
      obtain ⟨i₁, hi₁S, hi₁min⟩ := S.exists_min_image (fun i => c₀.2.1 i) hSne
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hi₁S
      refine ⟨c₀.2.1 i₁ - z.b₁, by linarith [hi₁S.2], fun i hi hib => ?_⟩
      have := hi₁min i (by simp [hS, hi, hib])
      linarith
    · push Not at hN
      exact ⟨1, one_pos, fun i hi hib => absurd (hN i hi) (not_le.2 hib)⟩
  have hb' : PiecewiseConstantBoundaryData.rightLim b z.b₁ = c₀.2.2 (z.k₄ c₀) := by
    refine InteractingSLE.Sec4.rightLim_eq_of_forall_notMem J (a := z.b₁ + ε) (by linarith) fun t ht htJ => ?_
    rw [← hb t htJ]
    have hidx : c₀.index t = z.k₄ c₀ := by
      refine BoundaryWord.index_eq_of_iff h4N fun i hi => ?_
      rw [lt_k₄_iff hc₀ hi]
      constructor
      · intro h
        by_contra h'
        have := hεJ i hi (not_le.1 h')
        linarith [ht.2]
      · intro h; exact lt_of_le_of_lt h ht.1
    unfold BoundaryWord.fn
    rw [hidx]
  rw [hb']
  -- right of `R₁` before the next position
  obtain ⟨δ, hδ, hδJ⟩ : ∃ δ > 0, ∀ i < (z.word c₀ g₁ g₂ g₃ g₄).1, z.m c₀ + 3 ≤ i →
      z.R₁ + δ ≤ (z.word c₀ g₁ g₂ g₃ g₄).2.1 i := by
    by_cases hN : ∃ i < (z.word c₀ g₁ g₂ g₃ g₄).1, z.m c₀ + 3 ≤ i
    · obtain ⟨i₀, hi₀, hi₀m⟩ := hN
      set S := (Finset.range (z.word c₀ g₁ g₂ g₃ g₄).1).filter fun i => z.m c₀ + 3 ≤ i with hS
      have hSne : S.Nonempty := ⟨i₀, by simp [hS, hi₀, hi₀m]⟩
      obtain ⟨i₁, hi₁S, hi₁min⟩ := S.exists_min_image (fun i => (z.word c₀ g₁ g₂ g₃ g₄).2.1 i) hSne
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hi₁S
      refine ⟨(z.word c₀ g₁ g₂ g₃ g₄).2.1 i₁ - z.R₁, by linarith [R₁_lt_pos hz hc₀ hi₁S.2 hi₁S.1],
        fun i hi him => ?_⟩
      have := hi₁min i (by simp [hS, hi, him])
      linarith
    · push Not at hN
      exact ⟨1, one_pos, fun i hi him => absurd him (not_le.2 (hN i hi))⟩
  refine InteractingSLE.Sec4.rightLim_eq_of_forall_notMem (z.word c₀ g₁ g₂ g₃ g₄).jumps (a := z.R₁ + δ) (by linarith)
    fun t ht _ => ?_
  unfold BoundaryWord.fn
  have hidx : (z.word c₀ g₁ g₂ g₃ g₄).index t = z.m c₀ + 3 := by
    refine BoundaryWord.index_eq_of_iff (by rw [word_fst]; omega) fun i hi => ?_
    rcases Nat.lt_or_ge i (z.m c₀ + 3) with h6 | h6
    · refine iff_of_true ?_ h6
      have hle : (z.word c₀ g₁ g₂ g₃ g₄).2.1 i ≤ z.R₁ := by
        rcases Nat.lt_or_ge i (z.m c₀ + 1) with hi1 | hi1
        · linarith [pos_le_L₁ hz hc₀ (g₁ := g₁) (g₂ := g₂) (g₃ := g₃) (g₄ := g₄) (show i ≤ z.m c₀ by omega),
            hz.L₁_le, hz.M₁_le]
        · obtain rfl | rfl : i = z.m c₀ + 1 ∨ i = z.m c₀ + 2 := by omega
          · rw [pos_m1]; exact hz.M₁_le
          · rw [pos_m2]
      exact lt_of_le_of_lt hle ht.1
    · exact iff_of_false (not_lt.2 ((hδJ i hi h6).trans' ht.2.le)) (by omega)
  rw [hidx, ht_right le_rfl, Nat.sub_self, zero_add]

end Datum

/-! ### Jumps -/

theorem mem_jumps_zone₀ {x : ℝ} (hx : x < z.a₂) (hj : x ∈ c₀.jumps) (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) :
    z.T x ∈ (z.word c₀ g₁ g₂ g₃ g₄).jumps := by
  obtain ⟨i, hi, hix⟩ := BoundaryWord.mem_jumps.1 hj
  have hik : i < z.k₁ c₀ := (lt_k₁_iff hc₀ hi).2 (hix ▸ hx)
  refine BoundaryWord.mem_jumps.2 ⟨i, by rw [word_fst]; unfold m; omega, ?_⟩
  rw [pos_of_lt hik, hix]

theorem mem_jumps_zone₁ (hz : z.Good) {x : ℝ} (hx : x ∈ Ioo z.b₂ z.a₁) (hj : x ∈ c₀.jumps)
    (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) : z.T x ∈ (z.word c₀ g₁ g₂ g₃ g₄).jumps := by
  obtain ⟨i, hi, hix⟩ := BoundaryWord.mem_jumps.1 hj
  have hi2 : z.k₂ c₀ ≤ i := by
    by_contra h
    have := (lt_k₂_iff hc₀ hi).1 (not_le.1 h)
    rw [hix] at this; linarith [hx.1]
  have hi3 : i < z.k₃ c₀ := (lt_k₃_iff hc₀ hi).2 (hix ▸ hx.2)
  have hk12 := k₁_le_k₂ (c₀ := c₀) hz
  refine BoundaryWord.mem_jumps.2 ⟨i - z.k₂ c₀ + (z.k₁ c₀ + 3), by rw [word_fst]; unfold m; omega, ?_⟩
  rw [pos_mid (by omega) (by unfold m; omega)]
  rw [show i - z.k₂ c₀ + (z.k₁ c₀ + 3) - (z.k₁ c₀ + 3) + z.k₂ c₀ = i by omega, hix]

theorem mem_jumps_zone₂ {x : ℝ} (hx : z.b₁ < x) (hj : x ∈ c₀.jumps) (hc₀ : StrictMonoOn c₀.2.1 (Iio c₀.1)) :
    z.T x ∈ (z.word c₀ g₁ g₂ g₃ g₄).jumps := by
  obtain ⟨i, hi, hix⟩ := BoundaryWord.mem_jumps.1 hj
  have hi4 : z.k₄ c₀ ≤ i := by
    by_contra h
    have := (lt_k₄_iff hc₀ hi).1 (not_le.1 h)
    rw [hix] at this; linarith
  refine BoundaryWord.mem_jumps.2 ⟨i - z.k₄ c₀ + (z.m c₀ + 3), by rw [word_fst]; omega, ?_⟩
  rw [pos_right (by omega)]
  rw [show i - z.k₄ c₀ + (z.m c₀ + 3) - (z.m c₀ + 3) + z.k₄ c₀ = i by omega, hix]

theorem R₁_mem_jumps : z.R₁ ∈ (z.word c₀ g₁ g₂ g₃ g₄).jumps :=
  BoundaryWord.mem_jumps.2 ⟨z.m c₀ + 2, by rw [word_fst]; omega, pos_m2⟩

end ZW

end Lemma76G

end Sec7

end InteractingSLE
