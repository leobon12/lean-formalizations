import HigherDimLQGMetric.Collapse.GeodesicCompact

/-! # Uniform continuity of the intrinsic metric on a compact collapse set -/

set_option autoImplicit false

open Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

theorem intrinsic_uniform_small {X : Type*} [MetricSpace X]
    {K : Set X} (hK : IsCompact K)
    (hKfin : ∀ p ∈ K, ∀ q ∈ K, internalEDist K p q ≠ ⊤)
    (hKcont : ContinuousOn (fun p : X × X => internalEDist K p.1 p.2) (K ×ˢ K)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ p ∈ K, ∀ q ∈ K, dist p q < δ → (internalEDist K p q).toReal < ε := by
  have hr : ContinuousOn
      (fun p : X × X => (internalEDist K p.1 p.2).toReal) (K ×ˢ K) :=
    ENNReal.continuousOn_toReal.comp hKcont
      (fun p hp => hKfin p.1 hp.1 p.2 hp.2)
  have hc := (hK.prod hK).uniformContinuousOn_of_continuous hr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hc ε hε
  refine ⟨δ, hδ, ?_⟩
  intro p hp q hq hpq
  have hpair : dist (p, q) (p, p) < δ := by
    simpa [Prod.dist_eq, dist_comm] using hpq
  have h := hmod (p, q) ⟨hp, hq⟩ (p, p) ⟨hp, hp⟩ hpair
  simpa [internalEDist_self hp, Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using h

end HigherDimLQGMetric
