import HigherDimLQGMetric.Bilip.ConditionalTail

/-!
# Geometry and regularity of separated Euclidean shells

The open shells in MA5 A17 are nice open sets and each lies outside the
closure of every other shell when `b*q < a`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

theorem bilip_shellNice {d : ℕ} (hd : 2 ≤ d) (z : Rd d) (a b : ℝ) :
    IsNiceOpen (shellOpen z a b) := by
  have : Nontrivial (Rd d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  constructor
  · exact (isBounded_ball : Bornology.IsBounded (ball z b)).subset Set.sdiff_subset
  · have hfr : frontier (ball z b \ closedBall z a) ⊆ sphere z b ∪ sphere z a := by
      have h := frontier_inter_subset (ball z b) (closedBall z a)ᶜ
      intro x hx
      have hx' : x ∈ frontier (ball z b ∩ (closedBall z a)ᶜ) := hx
      rcases h hx' with h1 | h2
      · exact Or.inl (frontier_ball_subset_sphere h1.1)
      · have h2' : x ∈ frontier (closedBall z a) := by simpa only [frontier_compl] using h2.2
        exact Or.inr (frontier_closedBall_subset_sphere h2')
    change volume (frontier (ball z b \ closedBall z a)) = 0
    exact measure_mono_null hfr
      (MeasureTheory.measure_union_null (Measure.addHaar_sphere volume z b)
        (Measure.addHaar_sphere volume z a))

theorem bilip_shell_small_outside_large_closure {d : ℕ} (z : Rd d)
    {a b a' b' : ℝ} (hgap : b' < a) :
    (shellOpen z a' b' : Set (Rd d)) ⊆
      (closure (shellOpen z a b : Set (Rd d)))ᶜ := by
  have hcl : closure (shellOpen z a b : Set (Rd d)) ⊆ (ball z a)ᶜ := by
    apply closure_minimal
    · intro x hx hball
      exact hx.2 (ball_subset_closedBall hball)
    · exact isOpen_ball.isClosed_compl
  intro x hx hxbig
  have hdist : dist x z < b' := by simpa only [mem_ball] using hx.1
  exact (hcl hxbig) (mem_ball.mpr (hdist.trans hgap))

theorem bilip_shell_large_outside_small_closure {d : ℕ} (z : Rd d)
    {a b a' b' : ℝ} (hgap : b' < a) :
    (shellOpen z a b : Set (Rd d)) ⊆
      (closure (shellOpen z a' b' : Set (Rd d)))ᶜ := by
  have hcl : closure (shellOpen z a' b' : Set (Rd d)) ⊆ closedBall z b' := by
    apply closure_minimal
    · exact Set.sdiff_subset.trans ball_subset_closedBall
    · exact isClosed_closedBall
  intro x hx hxsmall
  have hdist : a < dist x z := lt_of_not_ge (by
    intro hle
    exact hx.2 (by rwa [mem_closedBall]))
  have hdist' : b' < dist x z := hgap.trans hdist
  exact not_le_of_gt hdist' (by simpa only [mem_closedBall] using hcl hxsmall)

theorem bilip_shell_pairwise_outside_closure {d : ℕ} (z : Rd d)
    {a b q : ℝ} (ha1 : a < 1) (hb : 1 < b) (hq : 0 < q)
    (hgap : b * q < a) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hstep : ∀ i, r (i + 1) ≤ q * r i) (i j : ℕ) (hij : i ≠ j) :
    (shellOpen z (a * r j) (b * r j) : Set (Rd d)) ⊆
      (closure (shellOpen z (a * r i) (b * r i) : Set (Rd d)))ᶜ := by
  have hq1 : q < 1 := by
    calc q = 1 * q := (one_mul q).symm
      _ < b * q := mul_lt_mul_of_pos_right hb hq
      _ < a := hgap
      _ < 1 := ha1
  have hanti : Antitone r := antitone_nat_of_succ_le fun k =>
    (hstep k).trans (by simpa only [mul_comm] using
      mul_le_of_le_one_right (hr k).le hq1.le)
  have hsep (k l : ℕ) (hkl : k < l) : b * r l < a * r k := by
    have hl : r l ≤ q * r k :=
      (hanti (Nat.succ_le_of_lt hkl)).trans (hstep k)
    calc b * r l ≤ b * (q * r k) := mul_le_mul_of_nonneg_left hl (by linarith)
      _ = (b * q) * r k := by ring
      _ < a * r k := mul_lt_mul_of_pos_right hgap (hr k)
  rcases lt_or_gt_of_ne hij with hij' | hji
  · exact bilip_shell_small_outside_large_closure z (hsep i j hij')
  · exact bilip_shell_large_outside_small_closure z (hsep j i hji)

end HigherDimLQGMetric
