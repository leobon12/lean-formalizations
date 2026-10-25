import SupercriticalLQGUniqueness.B2.DG20Lim.CompleteFiniteComponent
import LQGMetric.Metric.Midpoint

 

set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.component_has_midpoints_of_large_annuli
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
        atTop (𝓝 (R.across O P)))
    (u : ℂ) :
    ∀ a b : FiniteComponent (R.toLSCMetric htri) u,
      ∃ z : FiniteComponent (R.toLSCMetric htri) u,
        LQGMetric.MetricGeometry.IsApproxMidpoint 0 a b z := by
  intro a b
  let M := R.toLSCMetric htri
  have hab : R.DfromR a.1 b.1 ≠ ∞ :=
    finiteComponent_edist_ne_top M u a b
  obtain ⟨z, haz, hbz⟩ :=
    R.exists_midpoint_le_half_of_large_annuli hlarge D hlen hcircle a.1 b.1 hab
  have hhalf : ENNReal.ofReal ((R.DfromR a.1 b.1).toReal / 2) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hazfin : R.DfromR a.1 z ≠ ∞ :=
    ne_top_of_le_ne_top hhalf haz
  have huz : R.DfromR u z ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
      ⟨ne_top_of_lt a.property, hazfin⟩) (htri u a.1 z)
  let zC : FiniteComponent M u := ⟨M.pt z, lt_top_iff_ne_top.mpr huz⟩
  refine ⟨zC, ?_⟩
  constructor
  · change (R.DfromR a.1 z).toReal ≤
      (R.DfromR a.1 b.1).toReal / 2 + 0
    rw [add_zero]
    have hh := ENNReal.toReal_mono hhalf haz
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (R.DfromR a.1 b.1).toReal / 2)] using hh
  · change (R.DfromR b.1 z).toReal ≤
      (R.DfromR a.1 b.1).toReal / 2 + 0
    rw [add_zero]
    have hh := ENNReal.toReal_mono hhalf hbz
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (R.DfromR a.1 b.1).toReal / 2)] using hh

end SupercriticalLQGUniqueness.B2.DG20Lim
