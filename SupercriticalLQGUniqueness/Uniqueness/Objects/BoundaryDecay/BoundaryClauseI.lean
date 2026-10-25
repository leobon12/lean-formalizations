import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay.BoundaryCircleCompare
import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay.BoundaryFailure




 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay

theorem annulus_bad_arclength_le_BBU
    (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) (g : LQGMetric.DistC)
    (c : ℂ) (s R : ℝ) (hs : 0 < s) :
    Objects.Shadow.circleOuter c s.toNNReal 0
      {x : ℂ | ∃ hx : x ∈ sphere c s,
        ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s c <
          annulusBoundaryCost (D g) (show s / 2 < s by linarith [hs]) ⟨x, hx⟩} ≤
      badBoundaryArclength ξ Q D c s R hs.le g := by
  have hs2 : 0 ≤ s / 2 := by positivity
  have hhalf : s / 2 < s := by linarith
  calc
    _ ≤ Objects.Shadow.circleOuter c s.toNNReal 0
      {x : ℂ | ∃ hx : x ∈ sphere c s,
        ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s c <
          ballBoundaryCost (D g) hs.le ⟨x, hx⟩} := by
        exact circleOuter_annulus_bad_le_ball_bad (D g) hs2 hhalf
    _ ≤ badBoundaryArclength ξ Q D c s R hs.le g :=
      circleOuter_ball_bad_le_badBoundaryArclength ξ Q D hD g c s R hs


theorem annulus_clauseI_failure_subset_bad_angle
    (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : Measurable D) (c : ℂ) (s R lam : ℝ)
    (hs : 0 < s) :
    {g : LQGMetric.DistC |
      ENNReal.ofReal s * ENNReal.ofReal (lam / 2) <
        Objects.Shadow.circleOuter c s.toNNReal 0
          {x : ℂ | ∃ hx : x ∈ sphere c s,
            ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s c <
              annulusBoundaryCost (D g) (show s / 2 < s by linarith [hs]) ⟨x, hx⟩}} ⊆
    {g : LQGMetric.DistC | ENNReal.ofReal (lam / 2) ≤
      ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ)
        ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))} := by
  intro g hg
  have hbound := annulus_bad_arclength_le_BBU ξ Q D hD g c s R hs
  have hs0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.mpr hs).ne'
  have hst : ENNReal.ofReal s ≠ ∞ := ENNReal.ofReal_ne_top
  have hlt : ENNReal.ofReal s * ENNReal.ofReal (lam / 2) <
      ENNReal.ofReal s *
        (∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ)
          ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))) := by
    exact hg.trans_le hbound
  exact ((ENNReal.mul_lt_mul_iff_right hs0 hst).mp hlt).le

theorem annulus_clauseI_failure_probability_decays
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ENNReal, C < ∞ ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ (c : ℂ) (s R : ℝ) (hs : 0 < s) (_hR : 0 < R),
          μ {g | ENNReal.ofReal s * ENNReal.ofReal (lam / 2) <
            Objects.Shadow.circleOuter c s.toNNReal 0
              {x : ℂ | ∃ hx : x ∈ sphere c s,
                ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s c <
                  annulusBoundaryCost (D g) (show s / 2 < s by linarith [hs]) ⟨x, hx⟩}} ≤
            ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ *
              (C / (ENNReal.ofReal R) ^ p)) / ENNReal.ofReal (lam / 2) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := bad_angle_failure_bound ξ Q hQ D hD lam hlam
  refine ⟨p, hp, C, hC, ?_⟩
  intro μ _ hh c s R hs hR
  exact (measure_mono (annulus_clauseI_failure_subset_bad_angle ξ Q D hD.1 c s R lam hs)).trans
    (hbound μ hh c s R hs hR)

theorem source_clauseI_threshold_eq (lam s : ℝ) (hs : 0 ≤ s) :
    ENNReal.ofReal ((lam / 2) * s) =
      ENNReal.ofReal s * ENNReal.ofReal (lam / 2) := by
  rw [mul_comm]
  exact ENNReal.ofReal_mul hs

theorem source_clauseI_failure_probability_decays
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ENNReal, C < ∞ ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ (c : ℂ) (s R : ℝ) (hs : 0 < s) (_hR : 0 < R),
          μ {g | ENNReal.ofReal ((lam / 2) * s) <
            Objects.Shadow.circleOuter c s.toNNReal 0
              {x : ℂ | ∃ hx : x ∈ sphere c s,
                ENNReal.ofReal R * Objects.AnnulusTails.nrm ξ Q g s c <
                  annulusBoundaryCost (D g) (show s / 2 < s by linarith [hs]) ⟨x, hx⟩}} ≤
            ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ *
              (C / (ENNReal.ofReal R) ^ p)) / ENNReal.ofReal (lam / 2) := by
  obtain ⟨p, hp, C, hC, hbound⟩ :=
    annulus_clauseI_failure_probability_decays ξ Q hQ D hD lam hlam
  refine ⟨p, hp, C, hC, ?_⟩
  intro μ _ hh c s R hs hR
  simpa only [source_clauseI_threshold_eq lam s hs.le] using
    (hbound μ hh c s R hs hR)


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay
