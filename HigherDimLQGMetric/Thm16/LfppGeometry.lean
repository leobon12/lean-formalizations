import HigherDimLQGMetric.Sec4.Basic

/-! Internal convolution LFPP dominates its unrestricted distance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l9c_ofReal_lfppDist_le_lfppDistIn {d : ℕ}
    (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d)
    (hφ : Continuous (convMollify κ ε h)) (V : Set (Rd d))
    (x y : Rd d) :
    ENNReal.ofReal (lfppDist κ ξ ε h (x, y)) ≤
      lfppDistIn κ ξ ε h V x y := by
  rw [lfppDistIn_eq_fieldDistIn]
  calc
    ENNReal.ofReal (lfppDist κ ξ ε h (x, y)) =
        fieldDistIn ξ (convMollify κ ε h) univ x y := by
      rw [fieldDistIn_eq_ofReal hφ
        (HigherDimLFPP.PcwJoined.of_convex convex_univ (mem_univ x) (mem_univ y))]
      rfl
    _ ≤ fieldDistIn ξ (convMollify κ ε h) V x y :=
      fieldDistIn_mono (subset_univ V)

theorem l9c_lfppSetDistIn_lower {d : ℕ}
    (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d)
    (hφ : Continuous (convMollify κ ε h)) (V A B : Set (Rd d))
    {L : ℝ} (hL : ∀ x ∈ A, ∀ y ∈ B, L ≤ lfppDist κ ξ ε h (x, y)) :
    ENNReal.ofReal L ≤ lfppSetDistIn κ ξ ε h V A B := by
  unfold lfppSetDistIn
  refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
  exact (ENNReal.ofReal_le_ofReal (hL x hx y hy)).trans
    (l9c_ofReal_lfppDist_le_lfppDistIn κ ξ ε h hφ V x y)

end HigherDimLQGMetric
