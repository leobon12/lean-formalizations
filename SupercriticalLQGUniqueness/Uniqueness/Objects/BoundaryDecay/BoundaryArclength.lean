import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay.DecayingBoundary




 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay

def badBoundaryArclength (ξ Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (c : ℂ) (s R : ℝ) (hs : 0 ≤ s) (g : LQGMetric.DistC) : ENNReal :=
  ENNReal.ofReal s *
    ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs (g, θ)
      ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))

theorem expected_bad_boundary_arclength_decays
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ENNReal, C < ∞ ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ (c : ℂ) (s R : ℝ) (hs : 0 < s) (_hR : 0 < R),
          (∫⁻ g, badBoundaryArclength ξ Q D c s R hs.le g ∂μ) ≤
            ENNReal.ofReal s * (C / (ENNReal.ofReal R) ^ p) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := expected_bad_angle_mass_decays ξ Q hQ D hD
  let A : ENNReal := (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ
  have hA : A < ∞ := by
    simpa only [A, Measure.restrict_apply_univ] using
      (measure_Icc_lt_top : volume (Icc (0 : ℝ) (2 * Real.pi)) < ∞)
  refine ⟨p, hp, A * C, ENNReal.mul_lt_top hA hC, ?_⟩
  intro μ _ hh c s R hs hR
  have hY : Measurable (fun g : LQGMetric.DistC =>
      ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ)
        ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))) :=
    Objects.BoundaryUnion.measurable_bad_angle_mass ξ Q D hD.1 c s R hs.le
  calc
    (∫⁻ g, badBoundaryArclength ξ Q D c s R hs.le g ∂μ) =
      ENNReal.ofReal s *
        (∫⁻ g, ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ)
          ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) ∂μ) := by
        exact lintegral_const_mul _ hY
    _ ≤ ENNReal.ofReal s * (A * (C / (ENNReal.ofReal R) ^ p)) :=
      mul_le_mul' le_rfl (hbound μ hh c s R hs hR)
    _ = ENNReal.ofReal s * (A * C / (ENNReal.ofReal R) ^ p) := by
      simp only [div_eq_mul_inv, mul_assoc]


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay
