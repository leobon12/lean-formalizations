import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.EndpointGeometry




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

theorem c45_closed_pair_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus) (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (hC45 : C45CorrectedNonemptyInternal P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs.radii objs.params objs.family)
    (μ : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1) :
    ∃ C : Set.Ioi (0 : ℝ), ∃ ε₀ : Set.Ioo (0 : ℝ) 1,
      ∀ ε : ℝ, (hε : 0 < ε) → ε ≤ ε₀ →
      ∀ (b : Set.Ioi (0 : ℝ)) (z w : ℂ) (s : ℝ),
        0 < s → s ≤ (b : ℝ) →
        z ∈ Metric.ball (0 : ℂ) b → w ∈ Metric.ball (0 : ℂ) b →
        (η : ℝ) * (b : ℝ) + 2 * s ≤ dist z w →
        (η : ℝ) * (b : ℝ) + s ≤ Metric.infDist z (Metric.sphere (0 : ℂ) b) →
        P (CountingBadEventV2 h D D' ξ Q cPlus objs.radii
          (fun z r hr => (objs.family z r hr).E) b ⟨ε, hε⟩
          (Metric.closedBall z s) (Metric.closedBall w s)) ≤
          ENNReal.ofReal ((C : ℝ) * ε ^ (μ : ℝ)) := by
  obtain ⟨C, ε₀, hC⟩ := hC45 μ η
  refine ⟨C, ε₀, ?_⟩
  intro ε hε hεle b z w s hs hsb hz hw hsep hclear
  have hηb : 0 < (η : ℝ) * (b : ℝ) := mul_pos η.property.1 b.property
  have hDisj : Disjoint (Metric.closedBall z s) (Metric.closedBall w s) :=
    closedBalls_disjoint_of_two_radius_lt z w s (by linarith only [hsep, hηb])
  apply hC ε hε hεle b (Metric.closedBall z s) (Metric.closedBall w s)
  · exact ⟨z, Metric.mem_closedBall_self hs.le⟩
  · exact ⟨w, Metric.mem_closedBall_self hs.le⟩
  · exact isCompact_closedBall z s
  · exact isCompact_closedBall w s
  · exact hDisj
  · exact closedBall_subset_double_origin z b s hz hsb
  · exact closedBall_subset_double_origin w b s hw hsb
  · exact euclidSetDist_closedBalls_ge z w s ((η : ℝ) * (b : ℝ)) hsep
  · exact euclidSetDist_closedBall_sphere_ge z b s ((η : ℝ) * (b : ℝ)) hclear

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
