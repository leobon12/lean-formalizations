import HigherDimLQGMetric.Limits.JointInternalConsistent
import HigherDimLQGMetric.Metric.WeylMetric

/-! The intrinsic internal coordinate determines an exterior Weyl metric. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- A common internal-limit coordinate and a common continuous Weyl field
determine the internal distance of the two Weyl-scaled ambient limits. -/
theorem l7a_internal_fiber_of_weyl {d : ℕ} (ξ : ℝ)
    {U : Set (Rd d)} (hU : IsOpen U)
    (E : C(U × U, ℝ)) (F : C(Rd d, ℝ))
    (D₁ D₁' D₂ D₂' : ContMetric d)
    (h₂ : ∃ hE : LQGMetric.MetricGeometry.IsMetricFun E,
      ∀ u v : U, D₂.internal U u.1 v.1 =
        LQGMetric.MetricGeometry.internalEDist univ
          (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE u)
          (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE v))
    (h₂' : ∃ hE : LQGMetric.MetricGeometry.IsMetricFun E,
      ∀ u v : U, D₂'.internal U u.1 v.1 =
        LQGMetric.MetricGeometry.internalEDist univ
          (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE u)
          (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE v))
    (hw : ∀ u v : Rd d,
      ENNReal.ofReal (D₁.1 (u,v)) = weylScale ξ F D₂ u v)
    (hw' : ∀ u v : Rd d,
      ENNReal.ofReal (D₁'.1 (u,v)) = weylScale ξ F D₂' u v)
    (u v : Rd d) : D₁.internal U u v = D₁'.internal U u v := by
  obtain ⟨hE, hcons⟩ := h₂
  obtain ⟨hE', hcons'⟩ := h₂'
  have he : hE' = hE := Subsingleton.elim _ _
  subst hE'
  have hbase : ∀ a ∈ U, ∀ b ∈ U,
      D₂.internal U a b = D₂'.internal U a b := by
    intro a ha b hb
    rw [hcons ⟨a, ha⟩ ⟨b, hb⟩, hcons' ⟨a, ha⟩ ⟨b, hb⟩]
  exact internal_weyl_eq_of_internal_eq (D₁ := D₂) (D₂ := D₂')
    (D₁' := D₁) (D₂' := D₁') hU hw hw' hbase
    (fun _ _ => rfl) u v

end HigherDimLQGMetric
