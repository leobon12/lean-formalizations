import SupercriticalLQGUniqueness.B2.DG20Lim.NestedFourChain

 

set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.nested_crossing_sum_le_across
    (R : RData) (B : ℕ → RatAnnulus)
    (hnest : ∀ n, (B n).inner.SurroundsCircle (B (n + 1)).outer)
    (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1),
      R.across (B n).inner (B n).outer) ≤
      R.across (B N).inner (B 0).outer := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hfour := R.two_edge_sum_le_across_of_nested
        (B (N + 1)).inner (B (N + 1)).outer
        (B N).inner (B 0).outer
        (B (N + 1)).nested (hnest N)
        (nested_annulus_outer_surrounds_later_inner B hnest N)
      calc
        (∑ n ∈ Finset.range (N + 1 + 1),
            R.across (B n).inner (B n).outer) =
          (∑ n ∈ Finset.range (N + 1),
            R.across (B n).inner (B n).outer) +
            R.across (B (N + 1)).inner (B (N + 1)).outer := by
              rw [Finset.sum_range_succ]
        _ ≤ R.across (B N).inner (B 0).outer +
            R.across (B (N + 1)).inner (B (N + 1)).outer :=
          add_le_add_left ih _
        _ = R.across (B (N + 1)).inner (B (N + 1)).outer +
            R.across (B N).inner (B 0).outer := by ac_rfl
        _ ≤ R.across (B (N + 1)).inner (B 0).outer := hfour

end SupercriticalLQGUniqueness.B2.DG20Lim
