import LQGMetric.Papers.DZZ.S3P32UClip
import LQGMetric.Papers.DZZ.S3P32UEnd

/-!
# DZZ P3.2 upper bound at the walled measure: geometry of the clipped boxes (D101, P-4a)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Proposition 3.2, upper bound
(l. 1088–1153, crossing of Lemma 3.5 l. 1054–1079), with the clipped rings of decision D101
(decisions/DEC-101.md §3): the covered curve of a ring box `B'` is `∂(B' ∩ 𝕍_{−r})`.

* `frontier_clip_eq`: for a box of side `> 2r`, `B ∩ 𝕍_{−r}` is the closed rectangle
  `[max a r, min a' (1−r)] × [max b r, min b' (1−r)]` and its boundary is the `rectBd` of it;
* `isPathConnected_frontier_clip`;
* `clampV_mem_frontier_clip`: the coordinatewise clamp `ℂ → 𝕍_{−r}` maps `∂B` into
  `∂(B ∩ 𝕍_{−r})`; hence meeting box boundaries give meeting clipped boundaries
  (`frontier_clip_meet`), and the chain of clipped boundaries of an enclosure is path-connected;
* `exists_cover_of_phiLeC`; `ball_endC` (the end argument `ball_end` with paths in `𝕍_{−r}`).

Own elementary arguments (DZZ do not clip; DV-D101).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

lemma isClosed_dzzVIn (r : ℝ) : IsClosed (dzzVIn r) := by
  have h1 : IsClosed {z : ℂ | r ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
  have h2 : IsClosed {z : ℂ | z.re ≤ 1 - r} := isClosed_le Complex.continuous_re continuous_const
  have h3 : IsClosed {z : ℂ | r ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have h4 : IsClosed {z : ℂ | z.im ≤ 1 - r} := isClosed_le Complex.continuous_im continuous_const
  exact h1.inter (h2.inter (h3.inter h4))

/-- The boundary of a closed rectangle is its `rectBd`. -/
lemma frontier_rect_eq {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    frontier {z : ℂ | a ≤ z.re ∧ z.re ≤ a' ∧ b ≤ z.im ∧ z.im ≤ b'} = rectBd a a' b b' := by
  have e : {z : ℂ | a ≤ z.re ∧ z.re ≤ a' ∧ b ≤ z.im ∧ z.im ≤ b'} = Icc a a' ×ℂ Icc b b' := by
    ext z; simp only [mem_ofPred_eq, Complex.mem_reProdIm, mem_Icc]; tauto
  rw [e, Complex.frontier_reProdIm, closure_Icc, closure_Icc, frontier_Icc ha, frontier_Icc hb]
  ext z
  simp only [mem_union, Complex.mem_reProdIm, mem_Icc, mem_insert_iff, mem_singleton_iff, rectBd,
    mem_ofPred_eq]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3 | h3⟩ | ⟨h3 | h3, ⟨h1, h2⟩⟩)
    · exact ⟨h1, h2, h3 ▸ le_rfl, h3 ▸ hb, Or.inr (Or.inr (Or.inl h3))⟩
    · exact ⟨h1, h2, h3 ▸ hb, h3 ▸ le_rfl, Or.inr (Or.inr (Or.inr h3))⟩
    · exact ⟨h3 ▸ le_rfl, h3 ▸ ha, h1, h2, Or.inl h3⟩
    · exact ⟨h3 ▸ ha, h3 ▸ le_rfl, h1, h2, Or.inr (Or.inl h3)⟩
  · rintro ⟨h1, h2, h3, h4, e | e | e | e⟩
    · exact Or.inr ⟨Or.inl e, h3, h4⟩
    · exact Or.inr ⟨Or.inr e, h3, h4⟩
    · exact Or.inl ⟨⟨h1, h2⟩, Or.inl e⟩
    · exact Or.inl ⟨⟨h1, h2⟩, Or.inr e⟩

/-- The coordinates of a box of side `> r` are compatible with `𝕍_{−r}`. -/
lemma box_coord_clip (B : DyBox) {r : ℝ} (hr : 2 * r < B.side) :
    (B.j : ℝ) * B.side ≤ 1 - r ∧ r ≤ ((B.j : ℝ) + 1) * B.side ∧
      (B.k : ℝ) * B.side ≤ 1 - r ∧ r ≤ ((B.k : ℝ) + 1) * B.side ∧ r ≤ 1 - r := by
  have hs := side_pos' B
  have h1 : ((B.j : ℝ) + 1) * B.side ≤ 1 := by
    have : ((B.j + 1 : ℕ) : ℝ) ≤ ((2 ^ B.n : ℕ) : ℝ) := by exact_mod_cast B.hj
    push_cast at this
    have e : (2 : ℝ) ^ B.n * B.side = 1 := by
      unfold DyBox.side; rw [← mul_pow]; norm_num
    nlinarith
  have h2 : ((B.k : ℝ) + 1) * B.side ≤ 1 := by
    have : ((B.k + 1 : ℕ) : ℝ) ≤ ((2 ^ B.n : ℕ) : ℝ) := by exact_mod_cast B.hk
    push_cast at this
    have e : (2 : ℝ) ^ B.n * B.side = 1 := by
      unfold DyBox.side; rw [← mul_pow]; norm_num
    nlinarith
  have hj0 : (0 : ℝ) ≤ B.j := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ B.k := Nat.cast_nonneg _
  have hs1 : B.side ≤ 1 := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by linarith⟩

/-- The clipped box is a closed rectangle. -/
lemma clip_eq (B : DyBox) (r : ℝ) :
    B.closedBox ∩ dzzVIn r = {z : ℂ | max (B.j * B.side) r ≤ z.re ∧
      z.re ≤ min ((B.j + 1) * B.side) (1 - r) ∧ max (B.k * B.side) r ≤ z.im ∧
      z.im ≤ min ((B.k + 1) * B.side) (1 - r)} := by
  ext z
  simp only [closedBox, dzzVIn, mem_inter_iff, mem_ofPred_eq, max_le_iff, le_min_iff]
  tauto

/-- **The boundary of the clipped box** `∂(B ∩ 𝕍_{−r})`. -/
lemma frontier_clip_eq (B : DyBox) {r : ℝ} (hr : 2 * r < B.side) :
    frontier (B.closedBox ∩ dzzVIn r) = rectBd (max (B.j * B.side) r)
      (min ((B.j + 1) * B.side) (1 - r)) (max (B.k * B.side) r)
      (min ((B.k + 1) * B.side) (1 - r)) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := box_coord_clip B hr
  have hs := side_pos' B
  rw [clip_eq]
  exact frontier_rect_eq (max_le (le_min (by nlinarith) c1) (le_min c2 c5))
    (max_le (le_min (by nlinarith) c3) (le_min c4 c5))

lemma isPathConnected_frontier_clip (B : DyBox) {r : ℝ} (hr : 2 * r < B.side) :
    IsPathConnected (frontier (B.closedBox ∩ dzzVIn r)) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := box_coord_clip B hr
  have hs := side_pos' B
  rw [frontier_clip_eq B hr]
  exact isPathConnected_rectBd (max_le (le_min (by nlinarith) c1) (le_min c2 c5))
    (max_le (le_min (by nlinarith) c3) (le_min c4 c5))

/-- The coordinatewise clamp to `[r, 1−r]`. -/
def clampR (r x : ℝ) : ℝ := max r (min x (1 - r))

/-- The coordinatewise clamp `ℂ → 𝕍_{−r}`. -/
def clampV (r : ℝ) (z : ℂ) : ℂ := ⟨clampR r z.re, clampR r z.im⟩

lemma clampR_props {r a a' x : ℝ} (h0 : r ≤ 1 - r) (h1 : a ≤ 1 - r) (h2 : r ≤ a')
    (hx1 : a ≤ x) (hx2 : x ≤ a') :
    max a r ≤ clampR r x ∧ clampR r x ≤ min a' (1 - r) ∧ (x = a → clampR r x = max a r) ∧
      (x = a' → clampR r x = min a' (1 - r)) := by
  unfold clampR
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [max_def, min_def]; split_ifs <;> linarith
  · simp only [max_def, min_def]; split_ifs <;> linarith
  · rintro rfl; simp only [max_def, min_def]; split_ifs <;> linarith
  · rintro rfl; simp only [max_def, min_def]; split_ifs <;> linarith

/-- **The clamp maps `∂B` into `∂(B ∩ 𝕍_{−r})`.** -/
lemma clampV_mem_frontier_clip (B : DyBox) {r : ℝ} (hr : 2 * r < B.side) {z : ℂ}
    (hz : z ∈ frontier B.closedBox) : clampV r z ∈ frontier (B.closedBox ∩ dzzVIn r) := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := box_coord_clip B hr
  rw [frontier_closedBox_eq] at hz
  rw [frontier_clip_eq B hr]
  obtain ⟨h1, h2, h3, h4, e⟩ := hz
  obtain ⟨p1, p2, p3, p4⟩ := clampR_props c5 c1 c2 h1 h2
  obtain ⟨q1, q2, q3, q4⟩ := clampR_props c5 c3 c4 h3 h4
  refine ⟨p1, p2, q1, q2, ?_⟩
  rcases e with e | e | e | e
  · exact Or.inl (p3 e)
  · exact Or.inr (Or.inl (p4 e))
  · exact Or.inr (Or.inr (Or.inl (q3 e)))
  · exact Or.inr (Or.inr (Or.inr (q4 e)))

/-- Meeting box boundaries give meeting clipped boundaries. -/
lemma frontier_clip_meet {B B' : DyBox} {r : ℝ} (hr : 2 * r < B.side) (hr' : 2 * r < B'.side)
    (h : (frontier B.closedBox ∩ frontier B'.closedBox).Nonempty) :
    (frontier (B.closedBox ∩ dzzVIn r) ∩ frontier (B'.closedBox ∩ dzzVIn r)).Nonempty := by
  obtain ⟨z, h1, h2⟩ := h
  exact ⟨clampV r z, clampV_mem_frontier_clip B hr h1, clampV_mem_frontier_clip B' hr' h2⟩

/-- The clipped boundaries of a chain of neighbouring boxes of one level are path-connected. -/
theorem isPathConnected_frontier_chainC {r : ℝ} : ∀ l : List DyBox, l ≠ [] →
    l.IsChain Neighbour → (∀ b ∈ l, ∀ b' ∈ l, b.n = b'.n) → (∀ b ∈ l, 2 * r < b.side) →
    IsPathConnected (⋃ b ∈ l, frontier (b.closedBox ∩ dzzVIn r))
  | [], h, _, _, _ => absurd rfl h
  | [a], _, _, _, hs => by
    simpa using isPathConnected_frontier_clip a (hs a List.mem_cons_self)
  | a :: b :: t, _, hch, hn, hs => by
    rw [List.isChain_cons_cons] at hch
    have ih := isPathConnected_frontier_chainC (b :: t) (List.cons_ne_nil _ _) hch.2
      (fun x hx y hy => hn x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      fun x hx => hs x (List.mem_cons_of_mem _ hx)
    have e : (⋃ x ∈ a :: b :: t, frontier (x.closedBox ∩ dzzVIn r)) =
        frontier (a.closedBox ∩ dzzVIn r) ∪ ⋃ x ∈ b :: t, frontier (x.closedBox ∩ dzzVIn r) := by
      simp only [List.mem_cons, iUnion_iUnion_eq_or_left]
    rw [e]
    refine (isPathConnected_frontier_clip a (hs a List.mem_cons_self)).union ih ?_
    have hb : b ∈ a :: b :: t := List.mem_cons_of_mem _ List.mem_cons_self
    obtain ⟨z, hz1, hz2⟩ := frontier_clip_meet (hs a List.mem_cons_self) (hs b hb)
      (frontier_inter_of_neighbour (hn a List.mem_cons_self b hb) hch.1)
    exact ⟨z, hz1, mem_biUnion List.mem_cons_self hz2⟩

end DZZ
end LQGMetric
