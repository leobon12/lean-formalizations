import SupercriticalLQGUniqueness.B2.DG20Lim.ComponentGeodesic
import SupercriticalLQGUniqueness.Frozen.LSCMetricIsLengthSpace

 


set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.lengthSpace_of_large_annuli
    (R : RData)
    (htri : ∀ x y z : ℂ,
      R.DfromR x z ≤ R.DfromR x y + R.DfromR y z)
    (hescape : ∀ u : ℂ, ∀ T : ℝ≥0∞, T ≠ ∞ →
      ∃ S : ℝ, ∀ v : ℂ, S ≤ dist v 0 → T ≤ R.DfromR u v)
    (hlarge : ∀ N : ℕ, ∃ r : {r : ℚ // 1 < r},
      (N : ℝ) < (r : ℚ) ∧
      ENNReal.ofReal ((N : ℝ) + 1) ≤ R.across
        (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property))
        (centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property)))
    (D : ℕ → LQGMetric.ContMetric) (hlen : ∀ n, (D n).IsLength)
    (hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
        atTop (𝓝 (R.across O P))) :
    (R.toLSCMetric htri).IsLengthSpace := by
  intro u v hfinite ε hε
  obtain ⟨γ, a, b, hγ, ha, hb, hlenγ⟩ :=
    R.exists_geodesic_of_large_annuli htri hescape hlarge
      D hlen hcircle u v hfinite
  exact ⟨γ, a, b, hγ, ha, hb, by
    rw [hlenγ]
    exact le_add_of_nonneg_right bot_le⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
