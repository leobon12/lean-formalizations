import SupercriticalConformalCovariance.Small.RegularConfinement

set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.Uniqueness

/-- The two dyadic endpoint tests in (8) supply the point and loop hypotheses of Lemma 4.1. -/
theorem sourceRegularPair_recovery_costs
    (D : LSCMetric) (u v : ℂ) (α θ m M δ : ℝ)
    (hreg : SupercriticalConformalCovariance.Regular.SourceRegularPair D 0 u v 1 α θ m)
    (hM : D (u,v) ≤ ENNReal.ofReal M)
    (hδ : ∃ j : ℕ, δ = SupercriticalConformalCovariance.Regular.dyadic j ∧
      0 < SupercriticalConformalCovariance.Regular.dyadic j ∧ SupercriticalConformalCovariance.Regular.dyadic j ≤ (1 - α) ^ 2)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hM0 : 0 ≤ M) :
    OptimalConstants.Ratios.setDist D {u} (sphere u δ) ≤
        ENNReal.ofReal (M * δ ^ θ) ∧
      OptimalConstants.Ratios.setDist D {v} (sphere v δ) ≤
        ENNReal.ofReal (M * δ ^ θ) ∧
      aroundDist D
          (SupercriticalConformalCovariance.Recovery.shortAnnulus u δ hδ0 hδ1) ≤
        ENNReal.ofReal (M * δ ^ θ) ∧
      aroundDist D
          (SupercriticalConformalCovariance.Recovery.shortAnnulus v δ hδ0 hδ1) ≤
        ENNReal.ofReal (M * δ ^ θ) := by
  obtain ⟨j,rfl,hj,hjα⟩ := hδ
  rcases hreg with ⟨_,_,_,_,h8u,h8v⟩
  obtain ⟨hpu,hlu⟩ := h8u j hj hjα
  obtain ⟨hpv,hlv⟩ := h8v j hj hjα
  simp only [mul_one] at hpu hlu hpv hlv
  have hpow : 0 ≤ (SupercriticalConformalCovariance.Regular.dyadic j) ^ θ :=
    Real.rpow_nonneg hj.le _
  have hm : ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j) ^ θ) * D (u,v) ≤
      ENNReal.ofReal (M * (SupercriticalConformalCovariance.Regular.dyadic j) ^ θ) := by
    calc
      _ ≤ ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j) ^ θ) * ENNReal.ofReal M :=
        by simpa only [mul_comm] using
          (mul_le_mul_left hM (ENNReal.ofReal ((SupercriticalConformalCovariance.Regular.dyadic j) ^ θ)))
      _ = ENNReal.ofReal (M * (SupercriticalConformalCovariance.Regular.dyadic j) ^ θ) := by
        rw [← ENNReal.ofReal_mul hpow]
        congr 1
        ring
  refine ⟨?_,?_,?_,?_⟩
  · rw [TwoScale.S36.setDist_singleton_eq_pointSphereDist]
    exact hpu.trans hm
  · rw [TwoScale.S36.setDist_singleton_eq_pointSphereDist]
    exact hpv.trans hm
  · rw [TwoScale.Consolidated.aroundDist_eq_aroundRat]
    simpa only [SupercriticalConformalCovariance.Recovery.shortAnnulus, EuclideanAnnulus.center,
      EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius] using hlu.trans hm
  · rw [TwoScale.Consolidated.aroundDist_eq_aroundRat]
    simpa only [SupercriticalConformalCovariance.Recovery.shortAnnulus, EuclideanAnnulus.center,
      EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius] using hlv.trans hm

end SupercriticalConformalCovariance.Small
