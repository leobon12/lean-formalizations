import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldEnergy
import SupercriticalLQGUniqueness.Uniqueness.Objects.Shield.ShieldLMCount




set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Shield

 

theorem exists_shield_marginal_energy
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants) :
    ∃ C₁ K₀ q : ℝ,
      1 ≤ C₁ ∧ 0 ≤ K₀ ∧
      q = Real.exp (-(K₀ ^ 2 *
        LQGMetric.gradEnergy (shieldAnnBump 1))) / 4 ∧
      0 < q ∧ q < 1 ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF
          (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∀ t : ℝ, 0 < t →
          ENNReal.ofReal q ≤ μ {g | Objects.Excursions.shieldAt C (D g) t} := by
  obtain ⟨C₁, K₀, q, hC₁, hK₀, hqdef, hq, hq1, hMarg⟩ :=
    exists_shield_marginal_center ξ Q D hD C
  refine ⟨C₁, K₀, q, hC₁, hK₀, ?_, hq, hq1, hMarg⟩
  rw [hqdef, gradEnergy_shieldAnnBump]

 

theorem exists_shield_failure_exp
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (C : Objects.CorrectedEvent.Constants) :
    ∃ C₁ K₀ q : ℝ,
      1 ≤ C₁ ∧ 0 ≤ K₀ ∧
      q = Real.exp (-(K₀ ^ 2 *
        LQGMetric.gradEnergy (shieldAnnBump 1))) / 4 ∧
      0 < q ∧ q < 1 ∧
      ∀ (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ],
        IsNormalizedWholePlaneGFF
          (id : LQGMetric.DistC → LQGMetric.DistC) μ →
        ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
          ∀ (T : Objects.CorrectedEvent.TubeData) (K : ℕ)
            (_hR : 0 < T.rho * T.r) (_hK : 1 ≤ K),
            μ {g | ¬ Objects.Excursions.shield C T K (D g)} ≤
              ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨C₁, K₀, q, hC₁, hK₀, hqdef, hq, hq1, hMarg⟩ :=
    exists_shield_marginal_energy ξ Q D hD C
  refine ⟨C₁, K₀, q, hC₁, hK₀, hqdef, hq, hq1, ?_⟩
  intro μ _ hμ
  exact shield_failure_le μ hμ ξ Q D hD C q hq hq1 (hMarg μ hμ)

end SupercriticalLQGUniqueness.Uniqueness.Objects.Shield
