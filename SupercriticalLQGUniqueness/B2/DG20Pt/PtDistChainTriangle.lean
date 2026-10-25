import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainCollar

 

set_option autoImplicit false
noncomputable section

open LQGMetric LQGMetric.LFPP
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_le_chain_sum
    (ξ : ℝ) (φ : ℂ → ℝ) (U : Set ℂ) (p : ℕ → ℂ) (N : ℕ) :
    lfppDOn ξ φ U (p 0) (p (N + 1)) ≤
      ∑ j ∈ Finset.range (N + 1), lfppDOn ξ φ U (p j) (p (j + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have htri := lfppDOn_triangle (ξ := ξ) (φ := φ) (S := U)
        (p 0) (p (N + 1)) (p (N + 2))
      calc
        lfppDOn ξ φ U (p 0) (p (N + 1 + 1))
            ≤ lfppDOn ξ φ U (p 0) (p (N + 1)) +
              lfppDOn ξ φ U (p (N + 1)) (p (N + 2)) := by simpa only [Nat.add_assoc] using htri
        _ ≤ (∑ j ∈ Finset.range (N + 1), lfppDOn ξ φ U (p j) (p (j + 1))) +
              lfppDOn ξ φ U (p (N + 1)) (p (N + 2)) := add_le_add ih le_rfl
        _ = ∑ j ∈ Finset.range (N + 1 + 1),
              lfppDOn ξ φ U (p j) (p (j + 1)) := by simp only [Finset.sum_range_succ]

end SupercriticalLQGUniqueness.B2.DG20Pt
