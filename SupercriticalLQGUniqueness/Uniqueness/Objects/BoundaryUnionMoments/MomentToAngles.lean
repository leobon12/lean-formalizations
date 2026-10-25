import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments.DyadicAround
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnion.BadAngleTonelli
import Mathlib.MeasureTheory.Integral.MeanInequalities




 





set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments

attribute [local irreducible] LSCMetric.internal

def normalizedBoundaryCost (ξ Q : ℝ)
    (D : LQGMetric.DistC → LSCMetric) (c : ℂ) (s : ℝ) (hs : 0 ≤ s)
    (θ : ℝ) (g : LQGMetric.DistC) : ENNReal :=
  (D g).internal (Metric.closedBall c s)
    (⟨circleMap c s θ, circleMap_mem_closedBall c hs θ⟩,
     ⟨c, Metric.mem_closedBall_self hs⟩) / Objects.AnnulusTails.nrm ξ Q g s c

theorem measurable_normalizedBoundaryCost (ξ Q : ℝ)
    (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    (c : ℂ) (s : ℝ) (hs : 0 ≤ s) (θ : ℝ) :
    Measurable (normalizedBoundaryCost ξ Q D c s hs θ) := by
  have hc : Measurable (fun g : LQGMetric.DistC =>
      (D g).internal (Metric.closedBall c s)
        (⟨circleMap c s θ, circleMap_mem_closedBall c hs θ⟩,
         ⟨c, Metric.mem_closedBall_self hs⟩)) := by
    have hpair : Measurable (fun g : LQGMetric.DistC => (g, θ)) :=
      measurable_id.prodMk measurable_const
    exact (Objects.BoundaryUnion.measurable_ball_boundary_cost D hD c s hs).comp hpair
  exact hc.div (Objects.BoundaryUnion.measurable_nrm ξ Q s c)

 

theorem expected_bad_angle_mass_le_of_moment
    (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric) (hD : Measurable D)
    (μ : Measure LQGMetric.DistC) [SFinite μ]
    (c : ℂ) (s R p : ℝ) (hs : 0 < s) (hR : 0 < R) (hp : 0 < p)
    (C : ENNReal)
    (hMoment : ∀ θ : ℝ,
      (∫⁻ g, normalizedBoundaryCost ξ Q D c s hs.le θ g ^ p ∂μ) ≤ C) :
    (∫⁻ g, ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ)
      ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) ∂μ) ≤
      (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ *
        (C / (ENNReal.ofReal R) ^ p) := by
  have hNpos (g : LQGMetric.DistC) : 0 < Objects.AnnulusTails.nrm ξ Q g s c := by
    unfold Objects.AnnulusTails.nrm
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (Real.rpow_pos_of_pos hs _) (Real.exp_pos _)
  have hNfinite (g : LQGMetric.DistC) : Objects.AnnulusTails.nrm ξ Q g s c ≠ ∞ := by
    unfold Objects.AnnulusTails.nrm
    exact ENNReal.ofReal_ne_top
  have hpoint (θ : ℝ) :
      μ {g | (g, θ) ∈ Objects.BoundaryUnion.badBoundaryRelation ξ Q D c s R hs.le} ≤
        C / (ENNReal.ofReal R) ^ p := by
    let Y := normalizedBoundaryCost ξ Q D c s hs.le θ
    have hY : AEMeasurable Y μ :=
      (measurable_normalizedBoundaryCost ξ Q D hD c s hs.le θ).aemeasurable
    have hsub : {g | (g, θ) ∈ Objects.BoundaryUnion.badBoundaryRelation ξ Q D c s R hs.le} ⊆
        {g | ENNReal.ofReal R ≤ Y g} := by
      intro g hg
      have hlt : ENNReal.ofReal R < Y g := by
        apply (ENNReal.lt_div_iff_mul_lt (Or.inl (hNpos g).ne')
          (Or.inl (hNfinite g))).2
        exact hg
      exact hlt.le
    have hmarkov : (ENNReal.ofReal R) ^ p *
        μ {g | ENNReal.ofReal R ≤ Y g} ≤ ∫⁻ g, Y g ^ p ∂μ := by
      have hm : AEMeasurable (fun g => Y g ^ p) μ := hY.pow_const p
      calc
        _ ≤ (ENNReal.ofReal R) ^ p * μ {g | (ENNReal.ofReal R) ^ p ≤ Y g ^ p} := by
          refine mul_le_mul' le_rfl (measure_mono ?_)
          intro g hg
          exact ENNReal.rpow_le_rpow hg hp.le
        _ ≤ ∫⁻ g, Y g ^ p ∂μ := mul_meas_ge_le_lintegral₀ hm _
    have hRpow0 : (ENNReal.ofReal R) ^ p ≠ 0 :=
      (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hR) ENNReal.ofReal_ne_top).ne'
    have hRpowtop : (ENNReal.ofReal R) ^ p ≠ ∞ := by
      exact ENNReal.rpow_ne_top_of_nonneg hp.le ENNReal.ofReal_ne_top
    apply (ENNReal.le_div_iff_mul_le (Or.inl hRpow0) (Or.inl hRpowtop)).2
    calc
      μ {g | (g, θ) ∈ Objects.BoundaryUnion.badBoundaryRelation ξ Q D c s R hs.le} *
          (ENNReal.ofReal R) ^ p ≤
        (ENNReal.ofReal R) ^ p * μ {g | ENNReal.ofReal R ≤ Y g} := by
          rw [mul_comm]
          exact mul_le_mul' le_rfl (measure_mono hsub)
      _ ≤ ∫⁻ g, Y g ^ p ∂μ := hmarkov
      _ ≤ C := hMoment θ
  exact Objects.BoundaryUnionDyadic.expected_bad_angle_mass_le_of_pointwise ξ Q D hD μ c s R hs.le
    (C / (ENNReal.ofReal R) ^ p) hpoint

end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments
