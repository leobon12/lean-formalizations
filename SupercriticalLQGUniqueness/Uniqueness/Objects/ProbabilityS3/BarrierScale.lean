import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RawLocalGen




 


set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem barrier_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞)
    (hscale : ∀ x y : ℂ, E (x,y) = c * D (x,y))
    (hB : BiLipschitz.Barrier.Barrier D) : BiLipschitz.Barrier.Barrier E := by
  intro n0 M
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hc0
    (show (M : ℝ≥0∞) ≠ ∞ by simp)
  obtain ⟨n, hn, hcross⟩ := hB n0 N
  refine ⟨n, hn, ?_⟩
  have hscaleCross := Positivity.Witnesses.acrossDist_eq_mul_of_dist_scale D E c hc0 hcTop
    hscale (BiLipschitz.Barrier.dyadicAnnulus n)
  calc
    (M : ℝ≥0∞) < (N : ℝ≥0∞) * c := hN
    _ = c * N := mul_comm _ _
    _ < c * acrossDist D (BiLipschitz.Barrier.dyadicAnnulus n) :=
      (ENNReal.mul_lt_mul_iff_right hc0 hcTop).mpr hcross
    _ = acrossDist E (BiLipschitz.Barrier.dyadicAnnulus n) := hscaleCross.symm

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
