import SupercriticalLQGUniqueness.B2.DG20Lim.LengthFromGeodesic
import SupercriticalLQGUniqueness.B2.DG20Lim.CompleteFromPointwiseEscape

 


set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.geometry_of_large_annuli
    (R : RData)
    (htri : ∀ x y z : ℂ,
      R.DfromR x z ≤ R.DfromR x y + R.DfromR y z)
    (hlarge : ∀ N : ℕ, ∃ r : {r : ℚ // 1 < r},
      (N : ℝ) < (r : ℚ) ∧
      ENNReal.ofReal ((N : ℝ) + 1) ≤ R.across
        (centeredInnerCircle 0 0 r.1 (lt_trans zero_lt_one r.property))
        (centeredOuterCircle 0 0 r.1 (lt_trans zero_lt_one r.property)))
    (D : ℕ → LQGMetric.ContMetric) (hlen : ∀ n, (D n).IsLength)
    (hcircle : ∀ O P : RatCircle,
      Tendsto (fun n => LQGMetric.Blueprint.setDist (D n) O.toSet P.toSet)
        atTop (𝓝 (R.across O P))) :
    (R.toLSCMetric htri).IsLengthSpace ∧
    (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
      ∀ v : ℂ, (R.toLSCMetric htri).1 (u, v) < ENNReal.ofReal η →
        dist u v < δ) ∧
    (∀ u v : ℂ, (R.toLSCMetric htri).1 (u, v) < ∞ →
      ∃ (γ : ℝ → ℂ) (a b : ℝ),
        (R.toLSCMetric htri).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
          (R.toLSCMetric htri).len γ a b = (R.toLSCMetric htri).1 (u, v)) := by
  have hescape : ∀ u : ℂ, ∀ T : ℝ≥0∞, T ≠ ∞ →
      ∃ S : ℝ, ∀ v : ℂ, S ≤ dist v 0 → T ≤ R.DfromR u v :=
    R.pointwise_escape_of_large_centered_annuli hlarge
  refine ⟨R.lengthSpace_of_large_annuli htri hescape hlarge D hlen hcircle,
    ?_, ?_⟩
  · intro u δ hδ
    exact R.euclidean_control_of_pointwise_escape hescape u δ hδ
  · intro u v hfinite
    exact R.exists_geodesic_of_large_annuli htri hescape hlarge
      D hlen hcircle u v hfinite

end SupercriticalLQGUniqueness.B2.DG20Lim
