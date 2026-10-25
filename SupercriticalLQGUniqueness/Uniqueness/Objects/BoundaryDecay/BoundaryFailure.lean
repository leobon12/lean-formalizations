import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay.DecayingBoundary




 


set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay

theorem bad_angle_failure_bound
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ p : ℝ, 0 < p ∧ ∃ C : ENNReal, C < ∞ ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ (c : ℂ) (s R : ℝ) (hs : 0 < s) (_hR : 0 < R),
          μ {g | ENNReal.ofReal (lam / 2) ≤
            ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ)
              ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))} ≤
            ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ *
              (C / (ENNReal.ofReal R) ^ p)) / ENNReal.ofReal (lam / 2) := by
  obtain ⟨p, hp, C, hC, hbound⟩ := expected_bad_angle_mass_decays ξ Q hQ D hD
  refine ⟨p, hp, C, hC, ?_⟩
  intro μ _ hh c s R hs hR
  let Y : LQGMetric.DistC → ENNReal := fun g =>
    ∫⁻ θ, Objects.BoundaryUnion.badPointIndicator ξ Q D c s R hs.le (g, θ)
      ∂(volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))
  have hY : AEMeasurable Y μ :=
    (Objects.BoundaryUnion.measurable_bad_angle_mass ξ Q D hD.1 c s R hs.le).aemeasurable
  have hTpos : 0 < ENNReal.ofReal (lam / 2) := ENNReal.ofReal_pos.mpr (by linarith)
  have hTtop : ENNReal.ofReal (lam / 2) ≠ ∞ := ENNReal.ofReal_ne_top
  apply (ENNReal.le_div_iff_mul_le (Or.inl hTpos.ne') (Or.inl hTtop)).2
  calc
    μ {g | ENNReal.ofReal (lam / 2) ≤ Y g} * ENNReal.ofReal (lam / 2) ≤
      ENNReal.ofReal (lam / 2) * μ {g | ENNReal.ofReal (lam / 2) ≤ Y g} := by rw [mul_comm]
    _ ≤ ∫⁻ g, Y g ∂μ := mul_meas_ge_le_lintegral₀ hY _
    _ ≤ (volume.restrict (Icc (0 : ℝ) (2 * Real.pi))) Set.univ *
          (C / (ENNReal.ofReal R) ^ p) := hbound μ hh c s R hs hR


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryDecay
