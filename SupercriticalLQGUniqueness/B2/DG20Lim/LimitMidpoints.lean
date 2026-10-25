import SupercriticalLQGUniqueness.B2.DG20Lim.MidpointLimit

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.exists_midpoint_le_half_of_large_annuli
    (R : RData)
    (hlarge : ∀ N : ℕ, ∃ r : {r : ℚ // 1 < r},
      (N : ℝ) < (r : ℚ) ∧
      ENNReal.ofReal ((N : ℝ) + 1) ≤ R.across
        (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property))
        (centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property)))
    (D : ℕ → LQGMetric.ContMetric) (hlen : ∀ n, (D n).IsLength)
    (hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
        atTop (𝓝 (R.across O P)))
    (u v : ℂ) (hfinite : R.DfromR u v ≠ ∞) :
    ∃ x : ℂ,
      R.DfromR u x ≤ ENNReal.ofReal ((R.DfromR u v).toReal / 2) ∧
      R.DfromR v x ≤ ENNReal.ofReal ((R.DfromR u v).toReal / 2) := by
  obtain ⟨zn, wn, hzn, hwn, hdist⟩ :=
    R.exists_pointDist_recovery D hcircle u v
  obtain ⟨xn, φ, x, hφ, hx, hmid⟩ :=
    R.exists_trapped_approx_midpoints hlarge D hlen hcircle
      u v hfinite zn wn hzn hwn hdist
  exact ⟨x, R.midpoint_bounds_of_trapped_subseq D hlen hcircle
    u v x hfinite zn wn xn φ hφ hzn hwn hx hdist hmid⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
