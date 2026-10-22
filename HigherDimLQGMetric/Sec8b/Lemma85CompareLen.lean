import HigherDimLQGMetric.Sec8b.Lemma85Remote
import HigherDimLQGMetric.Amplify.LengthScale

/-! Pointwise metric comparison extends to all path lengths. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

theorem s7b_compare_len (D E : ContMetric d) (C : ℝ) (hC : 0 < C)
    (hcomp : ∀ u v : Rd d, E.1 (u, v) ≤ C * D.1 (u, v))
    (P : ℝ → Rd d) (a b : ℝ) :
    E.len P a b ≤ (D.smul C hC).len P a b := by
  rw [E.len_def, (D.smul C hC).len_def,
    ← curveLengthWith_edist, ← curveLengthWith_edist]
  change curveLengthWith
      (fun u v : Rd d => edist (E.pt u) (E.pt v)) P a b ≤
    curveLengthWith
      (fun u v : Rd d => edist ((D.smul C hC).pt u)
        ((D.smul C hC).pt v)) P a b
  exact curveLengthWith_mono fun u v _ _ _ =>
    (by rw [E.edist_pt, (D.smul C hC).edist_pt]
        exact ENNReal.ofReal_le_ofReal (by
          simpa only [ContMetric.smul_apply] using hcomp (P u) (P v)))

end HigherDimLQGMetric
