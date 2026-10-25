import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay.BoundaryInfimum
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay.BoundaryArclength




 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay

theorem circleOuter_ball_bad_le_badBoundaryArclength
    (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) (g : LQGMetric.DistC)
    (c : ℂ) (s R : ℝ) (hs : 0 < s) :
    Objects.Shadow.circleOuter c s.toNNReal 0
      {x : ℂ | ∃ hx : x ∈ sphere c s,
        ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s c <
          ballBoundaryCost (D g) hs.le ⟨x, hx⟩} ≤
      badBoundaryArclength ξ Q D c s R hs.le g := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) (2 * Real.pi))
  let E : Set ℝ := {θ | (g, θ) ∈ Objects.BoundaryUnion.badBoundaryRelation ξ Q D c s R hs.le}
  have hE : MeasurableSet E := by
    exact (Objects.BoundaryUnion.measurableSet_bad_boundary_relation ξ Q D hD c s R hs.le).preimage
      (measurable_const.prodMk measurable_id)
  have hlin :
      (∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ) ∂ν) = ν E := by
    change (∫⁻ θ, E.indicator (fun _ => (1 : ENNReal)) θ ∂ν) = ν E
    exact lintegral_indicator_one hE
  have hsub :
      {θ ∈ Ico (0 : ℝ) (2 * Real.pi) |
        c + (s.toNNReal : ℂ) * Complex.exp (θ * Complex.I) ∈
          {x : ℂ | ∃ hx : x ∈ sphere c s,
            ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s c <
              ballBoundaryCost (D g) hs.le ⟨x, hx⟩}} ⊆ E ∩ Icc 0 (2 * Real.pi) := by
    intro θ hθ
    rcases hθ with ⟨hIco, hx⟩
    have hco : (s.toNNReal : ℂ) = (s : ℂ) := by
      exact_mod_cast Real.coe_toNNReal s hs.le
    rw [hco] at hx
    change (circleMap c s θ) ∈ _ at hx
    obtain ⟨hxs, hcost⟩ := hx
    refine ⟨?_, Ico_subset_Icc_self hIco⟩
    change ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s c <
      (D g).internal (closedBall c s)
        (⟨circleMap c s θ, circleMap_mem_closedBall c hs.le θ⟩,
         ⟨c, mem_closedBall_self hs.le⟩)
    exact hcost
  have hsub' :
      {θ ∈ Ico (0 : ℝ) (2 * Real.pi) |
        c + (s : ℂ) * Complex.exp (θ * Complex.I) ∈
          {x : ℂ | ∃ hx : x ∈ sphere c s,
            ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s c <
              ballBoundaryCost (D g) hs.le ⟨x, hx⟩}} ⊆ E ∩ Icc 0 (2 * Real.pi) := by
    simpa only [Real.coe_toNNReal s hs.le] using hsub
  unfold Objects.Shadow.circleOuter badBoundaryArclength
  simp only [Real.coe_toNNReal s hs.le, zero_add]
  apply mul_le_mul' le_rfl
  rw [hlin]
  simpa only [ν, Measure.restrict_apply hE, Set.inter_comm] using
    (measure_mono (μ := volume) hsub')


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay
