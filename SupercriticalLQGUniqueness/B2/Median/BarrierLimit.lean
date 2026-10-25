import SupercriticalLQGUniqueness.B2.Median.HeatShift

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 


theorem isCompact_infDist_thickening (N : Set ℂ)
    (hN : IsCompact N) (hne : N.Nonempty) (ρ : Set.Ioi (0 : ℝ)) :
    IsCompact {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)} := by
  have heq : {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)} =
      Metric.cthickening (ρ : ℝ) N := by
    ext z
    change Metric.infDist z N ≤ (ρ : ℝ) ↔
      Metric.infEDist z N ≤ ENNReal.ofReal (ρ : ℝ)
    exact (ENNReal.le_ofReal_iff_toReal_le
      (Metric.infEDist_ne_top hne) ρ.property.le).symm
  rw [heq]
  exact hN.cthickening

 


theorem separated_pair_in_infDist_thickening (N : Set ℂ)
    (hN : N.Nonempty) (ρ : Set.Ioi (0 : ℝ)) :
    ({p : ℂ × ℂ |
      Metric.infDist p.1 N ≤ (ρ : ℝ) ∧
      Metric.infDist p.2 N ≤ (ρ : ℝ) ∧
      (ρ : ℝ) / 2 ≤ dist p.1 p.2}).Nonempty := by
  obtain ⟨z, hz⟩ := hN
  let w : ℂ := z + ((ρ : ℝ) / 2 : ℂ)
  have hρ : (0 : ℝ) ≤ (ρ : ℝ) := ρ.property.le
  have hdist : dist z w = (ρ : ℝ) / 2 := by
    have hρhalf : 0 ≤ (ρ : ℝ) / 2 := by linarith only [hρ]
    simp [w, dist_eq_norm, Complex.norm_real]
    exact hρ
  refine ⟨(z, w), ?_, ?_, ?_⟩
  · simpa [Metric.infDist_zero_of_mem hz] using ρ.property.le
  · calc
      Metric.infDist w N ≤ dist w z := Metric.infDist_le_dist_of_mem hz
      _ = (ρ : ℝ) / 2 := by rw [dist_comm, hdist]
      _ ≤ (ρ : ℝ) := by linarith only [hρ]
  · exact hdist.ge

 

theorem exists_ball_for_infDist_thickening (N : Set ℂ)
    (hN : IsCompact N) (hne : N.Nonempty) (ρ : Set.Ioi (0 : ℝ)) :
    ∃ R : ℝ, 0 < R ∧
      {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)} ⊆ closedBall 0 R := by
  exact (isCompact_infDist_thickening N hN hne ρ).isBounded.subset_closedBall_lt 0 0

theorem eventually_crossing_le_shifted_path_of_barrier
    (ξ : Set.Ioi (0 : ℝ))
    (ε a : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (φ : ℕ → C(ℂ, ℝ)) (d : LSCMetric)
    (hG : Tendsto (fun n => lfppMetric (ξ : ℝ) (a n) (φ n)) atTop (𝓝 d))
    (N : Set ℂ) (ρ : Set.Ioi (0 : ℝ)) (M : ℝ) (hM : 0 < M)
    (R : ℝ) (hR : 0 < R)
    (hK : IsCompact {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)})
    (hKball : {z : ℂ | Metric.infDist z N ≤ (ρ : ℝ)} ⊆ closedBall 0 R)
    (hne : ({p : ℂ × ℂ |
      Metric.infDist p.1 N ≤ (ρ : ℝ) ∧
      Metric.infDist p.2 N ≤ (ρ : ℝ) ∧
      (ρ : ℝ) / 2 ≤ dist p.1 p.2}).Nonempty)
    (hstrip : ∀ z : ℂ, Metric.infDist z N ≤ (ρ : ℝ) →
      0 ≤ z.im ∧ z.im ≤ 1) :
    ∃ μ : ℝ≥0∞, 0 < μ ∧
      ∀ᶠ n in atTop, ∀ (P : ℝ → ℂ) (z w : ℂ),
        LQGMetric.IsPiecewiseC1Path P z w → z ∈ N →
        z.re ≤ 0 → 1 ≤ w.re →
        ENNReal.ofReal ((a n : ℝ)⁻¹) *
          LQGMetric.lfppLen (ξ : ℝ)
            (fun u => φ n u +
              LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
                (penaltyField N ρ M) M (penaltyField_abs_le N ρ hM.le) u) P
          < ENNReal.ofReal (Real.exp ((ξ : ℝ) * (M / 4))) * μ →
        ENNReal.ofReal ((a n : ℝ)⁻¹) *
          lfppCrossingLength (ξ : ℝ) (φ n) ≤
        ENNReal.ofReal ((a n : ℝ)⁻¹) *
          LQGMetric.lfppLen (ξ : ℝ)
            (fun u => φ n u +
              LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
                (penaltyField N ρ M) M (penaltyField_abs_le N ρ hM.le) u) P := by
  obtain ⟨μ, hμ, hsep⟩ :=
    Uniqueness.Toolkit.PathInfimum.eventually_separated_pairs_pos
      hG hK (div_pos ρ.property (by norm_num)) hne
  have hheat := eventually_penaltyField_heatMollify_ge ε hε N ρ M hM R hR
  refine ⟨μ, hμ, ?_⟩
  filter_upwards [hsep, hheat] with n hn hhn P z w hP hzN hz hw hcost
  let ψ : C(ℂ, ℝ) := LQGMetric.LFPP.mollCont (ε n : ℝ) (ε n).property.ne'
    (penaltyField N ρ M) M (penaltyField_abs_le N ρ hM.le)
  have hψ : ∀ u ∈ Icc (0 : ℝ) 1,
      1 / 2 ≤ distanceRatio N ρ (P u) →
      distanceRatio N ρ (P u) ≤ 1 → M / 4 ≤ ψ (P u) := by
    intro u _ hu huone
    have hthick : Metric.infDist (P u) N ≤ (ρ : ℝ) := by
      simpa only [one_mul] using (div_le_iff₀ ρ.property).mp huone
    exact hhn (P u) (hKball hthick) hu
  have hψnonneg : ∀ u : ℂ, 0 ≤ ψ u := by
    intro u
    exact heatMollify_nonneg_of_nonneg (penaltyField N ρ M) M
      (penaltyField_abs_le N ρ hM.le)
      (penaltyField_nonneg N ρ hM.le) (ε n) u
  have hmetric : ∀ u v : ℂ,
      Metric.infDist u N ≤ (ρ : ℝ) →
      Metric.infDist v N ≤ (ρ : ℝ) →
      (ρ : ℝ) / 2 ≤ dist u v →
      μ ≤ lfppMetric (ξ : ℝ) (a n) (φ n) (u, v) := by
    intro u v hu hv huv
    exact hn (u, v) hu hv huv
  have hpathstrip : ∀ u ∈ Icc (0 : ℝ) 1,
      distanceRatio N ρ (P u) < 1 →
        0 ≤ (P u).im ∧ (P u).im ≤ 1 := by
    intro u _ hu
    apply hstrip
    have hu' : Metric.infDist (P u) N < (ρ : ℝ) := by
      simpa only [one_mul] using (div_lt_iff₀ ρ.property).mp hu
    exact hu'.le
  exact crossing_le_shifted_path_of_barrier ξ.property.le (a n)
    (φ n) ψ N ρ μ hP hzN hz hw hmetric hψ hψnonneg hpathstrip hcost

end SupercriticalLQGUniqueness.B2.Median
