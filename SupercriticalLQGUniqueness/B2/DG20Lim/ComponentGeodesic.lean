import SupercriticalLQGUniqueness.B2.DG20Lim.ComponentMidpoints
import LQGMetric.Metric.Midpoint

 


set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.exists_geodesic_of_large_annuli
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
        atTop (𝓝 (R.across O P)))
    (u v : ℂ) (hfinite : R.DfromR u v < ∞) :
    ∃ (γ : ℝ → ℂ) (a b : ℝ),
      (R.toLSCMetric htri).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
      (R.toLSCMetric htri).len γ a b = R.DfromR u v := by
  let M := R.toLSCMetric htri
  letI : CompleteSpace (FiniteComponent M u) :=
    R.complete_finiteComponent_of_pointwise_escape htri hescape u
  let a : FiniteComponent M u := ⟨M.pt u, by simp⟩
  let b : FiniteComponent M u := ⟨M.pt v, hfinite⟩
  have hm : ∀ p q : FiniteComponent M u,
      ∃ z : FiniteComponent M u,
        LQGMetric.MetricGeometry.IsApproxMidpoint 0 p q z :=
    R.component_has_midpoints_of_large_annuli htri hlarge D hlen hcircle u
  obtain ⟨P, hP0, hP1, hLip⟩ :=
    LQGMetric.MetricGeometry.exists_lipschitz_curve_of_midpoints
      (ε := (0 : ℝ)) a b (by norm_num)
      (fun n p q => by simpa using hm p q)
  obtain ⟨hCont, hLen⟩ :=
    LQGMetric.MetricGeometry.curveLength_le_of_dist_le_mul
      (C := dist a b) dist_nonneg (by simpa only [add_zero] using hLip)
  let γ : ℝ → ℂ := fun t => (P t).1
  refine ⟨γ, 0, 1, ?_, ?_, ?_, ?_⟩
  · constructor
    · norm_num
    · exact continuous_subtype_val.comp_continuousOn hCont
  · change (P 0).1 = u
    rw [hP0]
    rfl
  · change (P 1).1 = v
    rw [hP1]
    rfl
  · have hEq : M.len γ 0 1 = LQGMetric.MetricGeometry.curveLength P 0 1 := by
      rfl
    rw [hEq]
    apply le_antisymm
    · exact hLen.trans_eq (by rw [← edist_dist]; rfl)
    · have hLower := LQGMetric.MetricGeometry.edist_le_curveLength P
        (show (0 : ℝ) ≤ 1 by norm_num)
      rw [hP0, hP1] at hLower
      change R.DfromR u v ≤ LQGMetric.MetricGeometry.curveLength P 0 1 at hLower
      exact hLower

end SupercriticalLQGUniqueness.B2.DG20Lim
