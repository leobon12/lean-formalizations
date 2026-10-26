import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.QPosBridgeV2
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3

/-! Escape of the metric distance from a fixed Euclidean ball to large Euclidean spheres. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLFPPAS

open SupercriticalLQGUniqueness
open LQGMetric (DistC IsGFFPlusCont IsWholePlaneGFF)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier

/-- The barrier gives a uniform escape bound from a Euclidean ball to every sufficiently
large concentric sphere. -/
theorem d2EscapeSetDist_eventually_gt_of_barrier (D : LSCMetric)
    (hB : Barrier D) (hL : D.IsLengthSpace) (k M : ℕ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (M : ℝ≥0∞) < SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
        D (Metric.closedBall (0 : ℂ) k)
        (Metric.sphere (0 : ℂ) R) := by
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (k : ℝ) (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨n, hn, hcross⟩ := hB n₀ (M + 1)
  refine ⟨(2 : ℝ) ^ (n + 1), fun R hR => ?_⟩
  have hkn : (k : ℝ) ≤ (2 : ℝ) ^ n := hn₀.le.trans (pow_le_pow_right₀ one_le_two hn)
  have hcross' : acrossDist D (dyadicAnnulus n) ≤
      SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
        D (Metric.closedBall (0 : ℂ) k)
        (Metric.sphere (0 : ℂ) R) := by
    unfold SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
    refine le_iInf fun x => le_iInf fun hx => le_iInf fun y => le_iInf fun hy => ?_
    have hxnorm : ‖x‖ ≤ (2 : ℝ) ^ n := by
      have hx' : dist x 0 ≤ (k : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hx
      simpa only [dist_zero_right] using hx'.trans hkn
    have hynorm : (2 : ℝ) ^ (n + 1) ≤ ‖y‖ := by
      have hy' : dist y 0 = R := by
        simpa only [Metric.mem_sphere] using hy
      rw [← dist_zero_right, hy']
      exact hR
    have hpoint : acrossDist D (dyadicAnnulus n) ≤ D (x, y) := by
      rw [acrossDist_eq_iInf_internal D hB hL (dyadicAnnulus n)
        (Y := Set.univ) (subset_univ _)]
      apply iInf_internal_le D hB hL (dyadicAnnulus n).2.2.le (subset_univ _)
      · change ‖x - (0 : ℂ)‖ ≤ (2 : ℝ) ^ n
        simpa only [sub_zero] using hxnorm
      · change (2 : ℝ) ^ (n + 1) ≤ ‖y - (0 : ℂ)‖
        simpa only [sub_zero] using hynorm
    exact hpoint
  have hMlt : (M : ℝ≥0∞) < ((M + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (Nat.lt_succ_self M)
  have hcrossNat : ((M + 1 : ℕ) : ℝ≥0∞) < acrossDist D (dyadicAnnulus n) := by
    exact_mod_cast hcross
  exact (hMlt.trans hcrossNat).trans_le hcross'

/-- Almost surely, for each integer `k`, the distance from the closed Euclidean `k`-ball to
concentric spheres tends to infinity, expressed by its natural-threshold formulation. -/
theorem ae_d2EscapeSetDist {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ k M : ℕ, ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (M : ℝ≥0∞) < SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.setDist
        (D (h ω))
        (Metric.closedBall (0 : ℂ) k)
        (Metric.sphere (0 : ℂ) R) := by
  have hplus : IsGFFPlusCont h P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh.1
  have hQ : 0 < Q :=
    SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.q_pos_of_weak_metric
      ξ Q D hD
  have hlength := hD.2.1 P h hplus
  have hbarrier := ae_barrier hD hQ P h hh
  filter_upwards [hlength, hbarrier] with ω hL hB
  intro k M
  exact d2EscapeSetDist_eventually_gt_of_barrier (D (h ω)) hB hL k M

end SupercriticalLFPPAS
