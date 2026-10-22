import HigherDimLQGMetric.Limits.JointInternalConsistent
import HigherDimLQGMetric.Weak.DetInternalTight

/-! Compactness of internal distances along an ambient convergent sequence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Filter Topology Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- An ambient compact-open limit gives relative compactness of the internal
distances on each connected open domain. -/
theorem l6c_internal_relcompact_of_ambient_tendsto {d : ℕ}
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hamb : Tendsto (fun n => (Dn n).1) atTop (𝓝 D.1))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    IsCompact (closure (Set.range
      (fun n => internalC (Dn n) (hDn n) hU hUc))) := by
  have hconv : ∀ R : ℝ, 0 < R →
      TendstoUniformlyOn (fun n => ⇑(Dn n).1) ⇑D.1 atTop
        (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := by
    intro R _
    exact (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hamb) _
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  exact isCompact_closure_range_internalC Dn D hDn hconv hU hUc

/-- Every subsequential internal limit is a compatible genuine metric on the
domain. -/
theorem l6c_internal_subseq_consistent {d : ℕ}
    (Dn : ℕ → ContMetric d) (D : ContMetric d)
    (hDn : ∀ n, (Dn n).IsLength)
    (hamb : Tendsto (fun n => (Dn n).1) atTop (𝓝 D.1))
    {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsPreconnected U) :
    ∃ E : C(U × U, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => internalC (Dn (φ n)) (hDn (φ n)) hU hUc)
        atTop (𝓝 E) ∧
      ∃ hE : LQGMetric.MetricGeometry.IsMetricFun E,
        Continuous (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE) ∧
        Continuous (metricFunSpaceValU E hE) ∧
        ∀ u v : U, D.internal U u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist Set.univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt E hE v) := by
  letI := hU.locallyCompactSpace
  letI : PolishSpace C(U × U, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  obtain ⟨E, -, φ, hφ, hE⟩ :=
    (l6c_internal_relcompact_of_ambient_tendsto Dn D hDn hamb hU hUc).tendsto_subseq
      (x := fun n => internalC (Dn n) (hDn n) hU hUc)
      (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨E, φ, hφ, hE, ?_⟩
  exact l6c_internal_limit_consistent (fun n => Dn (φ n)) D
    (fun n => hDn (φ n)) (hamb.comp hφ.tendsto_atTop) hU hUc E hE

end HigherDimLQGMetric
