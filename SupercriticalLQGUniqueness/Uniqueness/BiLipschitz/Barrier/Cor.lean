import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Prob
import LQGMetric.Papers.GM.S1.Subseq




 












set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness
namespace Uniqueness.BiLipschitz.Barrier

open LQGMetric (DistC IsWholePlaneGFF IsGFFPlusCont)

 

theorem lt_dist_of_barrier (D : LSCMetric) (hB : Barrier D) (hL : D.IsLengthSpace) (z : ℂ)
    (M : ℕ) : ∃ R₀ : ℝ, ∀ w : ℂ, R₀ ≤ ‖w‖ → (M : ℝ≥0∞) < D (z, w) := by
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt ‖z‖ (one_lt_two : (1 : ℝ) < 2)
  obtain ⟨n, hn, hacross⟩ := hB n₀ M
  refine ⟨(2 : ℝ) ^ (n + 1), fun w hw => hacross.trans_le ?_⟩
  have hz : ‖z - (dyadicAnnulus n).center‖ ≤ (dyadicAnnulus n).innerRadius := by
    show ‖z - 0‖ ≤ (2 : ℝ) ^ n
    rw [sub_zero]
    exact hn₀.le.trans (pow_le_pow_right₀ one_le_two hn)
  have hw' : (dyadicAnnulus n).outerRadius ≤ ‖w - (dyadicAnnulus n).center‖ := by
    show (2 : ℝ) ^ (n + 1) ≤ ‖w - 0‖
    rw [sub_zero]
    exact hw
  rw [acrossDist_eq_iInf_internal D hB hL (dyadicAnnulus n) (Y := univ) (subset_univ _)]
  exact iInf_internal_le D hB hL (c := (dyadicAnnulus n).center)
    (r₁ := (dyadicAnnulus n).innerRadius) (r₂ := (dyadicAnnulus n).outerRadius)
    (dyadicAnnulus n).2.2.le (subset_univ _) hz hw'

 

theorem isBounded_closedBall_of_barrier (D : LSCMetric) (hB : Barrier D)
    (hL : D.IsLengthSpace) (z : ℂ) (M : ℝ≥0∞) (hM : M ≠ ⊤) :
    Bornology.IsBounded {w : ℂ | D (z, w) ≤ M} := by
  obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hM
  obtain ⟨R₀, hR₀⟩ := lt_dist_of_barrier D hB hL z m
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R₀)).subset fun w hw => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hfar
  exact absurd ((hR₀ w (not_le.1 hfar).le).trans_le hw) (not_lt.2 hm.le)

 



theorem ae_curves_continuous {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsWeakLQGMetric ξ Q D) (hQ : 0 < Q)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, Continuous (forget (D (h ω))) ∧
      (∀ (γ : ℝ → ℂ) (a b : ℝ), (D (h ω)).IsCurve γ a b → ContinuousOn γ (Icc a b)) ∧
      (∀ (z : ℂ) (M : ℝ≥0∞), M ≠ ⊤ → Bornology.IsBounded {w : ℂ | D (h ω) (z, w) ≤ M}) := by
  have hplus : IsGFFPlusCont h P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh.1
  filter_upwards [ae_barrier hD hQ P h hh, hD.2.1 P h hplus] with ω hB hL
  exact ⟨continuous_forget_of_barrier _ hB hL,
    fun γ a b hγ => continuousOn_of_barrier_of_length _ hB hL hγ,
    fun z M hM => isBounded_closedBall_of_barrier _ hB hL z M hM⟩

end Uniqueness.BiLipschitz.Barrier
end SupercriticalLQGUniqueness
