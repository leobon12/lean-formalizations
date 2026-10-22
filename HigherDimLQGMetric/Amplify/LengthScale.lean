import HigherDimLQGMetric.Events.ScaledEvent

/-! Path length under the affine and scalar metric changes used at trial scale. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry
open scoped ENNReal

variable {d : ℕ}

theorem amplify_len_affine (D : ContMetric d) {r : ℝ} (hr : r ≠ 0)
    (z : Rd d) (P : ℝ → Rd d) (a b : ℝ) :
    (D.affine r hr z).len P a b =
      D.len (fun t => r • P t + z) a b := by
  rw [ContMetric.len_def, ContMetric.len_def,
    ← curveLengthWith_edist, ← curveLengthWith_edist]
  unfold curveLengthWith
  congr 1

theorem amplify_len_smul (D : ContMetric d) {c : ℝ} (hc : 0 < c)
    (P : ℝ → Rd d) (a b : ℝ) :
    (D.smul c hc).len P a b = ENNReal.ofReal c * D.len P a b := by
  rw [ContMetric.len_def, ContMetric.len_def,
    ← curveLengthWith_edist, ← curveLengthWith_edist,
    ← curveLengthWith_const_mul]
  exact curveLengthWith_congr fun u v _ _ _ => D.edist_smul c hc (P u) (P v)

/-- A sharp centered metric gives the original path length divided by its
random normalizer after moving the path into physical coordinates. -/
theorem amplify_len_sharpScaledMetric (ξ Q : ℝ)
    (D : DistRd d → ContMetric d) (X : DistRd d)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (P : ℝ → Rd d) :
    (weakScaledMetric ξ D (fun t => t ^ (ξ * Q)) X hr z
      (Real.rpow_pos_of_pos hr _)).len P 0 1 =
      ENNReal.ofReal ((sNorm ξ Q X r z)⁻¹) *
        (D X).len (fun t => r • P t + z) 0 1 := by
  unfold weakScaledMetric
  rw [amplify_len_smul, amplify_len_affine, sharpScaledCoeff]

end HigherDimLQGMetric
