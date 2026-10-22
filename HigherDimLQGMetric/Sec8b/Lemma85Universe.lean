import HigherDimLQGMetric.Sec8.Events
import HigherDimLQGMetric.Sharp.GridCount
import HigherDimLQGMetric.Sec8b.SmallSubsets

/-! The finite lattice universe of a fixed scale and trap-label family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Classical Set Metric
open HigherDimLFPP (Rd)
open HigherDimLFPP.DGZ (latPt)

variable {d : ℕ}

def s7b_siteUniverse (d J : ℕ) (r R : ℝ) : Finset (Rd d × ℕ) :=
  (shellGridBox d (⌈5 * R / (r / (100 * d))⌉₊ + 1)
    (r / (100 * d))).product (Finset.range J)

theorem s7b_labeled_subset_universe {J : ℕ} (hd : 1 ≤ d)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    {x y : Rd d} {colour : Fin d → ℤ}
    {Z : Finset (Rd d × ℕ)}
    (hZ : IsSec8LabeledSet d J r R x y colour Z) :
    Z ⊆ s7b_siteUniverse d J r R := by
  intro site hsite
  obtain ⟨k, hk, _, hcenter, _, _, hlabel⟩ := hZ.1 site hsite
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hs : 0 < r / (100 * (d : ℝ)) := by positivity
  have hgrid : site.1 ∈ gridPts (r / (100 * d)) := by
    refine ⟨k, ?_⟩
    rw [hk]
    rfl
  have hball : site.1 ∈ ball (0 : Rd d) (5 * R) := by
    simpa only [mem_ball_zero_iff] using hcenter
  have hbox := grid_ball_subset_shellGridBox hs
    (show 0 ≤ 5 * R by positivity) ⟨hgrid, hball⟩
  exact Finset.mem_product.mpr
    ⟨Finset.mem_coe.mp hbox, Finset.mem_range.mpr hlabel⟩

theorem s7b_siteUniverse_card_le (d J : ℕ) (r R : ℝ) :
    (s7b_siteUniverse d J r R).card ≤
      (2 * (⌈5 * R / (r / (100 * d))⌉₊ + 1) + 1) ^ d * J := by
  unfold s7b_siteUniverse
  change (shellGridBox d (⌈5 * R / (r / (100 * d))⌉₊ + 1)
    (r / (100 * d)) ×ˢ Finset.range J).card ≤ _
  rw [Finset.card_product, Finset.card_range]
  exact Nat.mul_le_mul_right J (card_shellGridBox_le d _ _)

/-- A fixed class has at most polynomially many candidate sets of size at
most `k`. -/
theorem s7b_labeled_family_card_le {J : ℕ} (hd : 1 ≤ d)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (x y : Rd d) (colour : Fin d → ℤ) (k : ℕ)
    (S : Finset (Finset (Rd d × ℕ)))
    (hS : ∀ Z ∈ S, IsSec8LabeledSet d J r R x y colour Z ∧ Z.card ≤ k) :
    S.card ≤ (k + 1) * ((s7b_siteUniverse d J r R).card + 1) ^ k := by
  exact s7b_card_small_subsets_le (s7b_siteUniverse d J r R) S k
    (fun Z hZ => ⟨s7b_labeled_subset_universe hd hr hR (hS Z hZ).1,
      (hS Z hZ).2⟩)

end HigherDimLQGMetric
