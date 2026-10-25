import SupercriticalLQGUniqueness.B2.DG20Lim.LargeCircleAverageTail

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_large_circle_average_lower_tail
    (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (β η : ℝ) (hβ : 0 < β) (hη : 0 < η) :
    ∃ R₀ : ℝ, 1 < R₀ ∧ ∀ r : Ioi (1 : ℝ), R₀ ≤ (r : ℝ) →
      μ {g | circleAvg (affineComp (r : ℝ) 0 g) 1 0 ≤
        -(β * Real.log (r : ℝ))} ≤ ENNReal.ofReal η := by
  have hp : 0 < β ^ 2 / 2 := by positivity
  have hpow : Tendsto (fun r : ℝ => 2 * r ^ (-(β ^ 2 / 2))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop hp).const_mul 2
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1
    (hpow.eventually (Iio_mem_nhds hη))
  refine ⟨max R 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro r hr
  have hrR : R ≤ (r : ℝ) := (le_max_left _ _).trans hr
  calc
    μ {g | circleAvg (affineComp (r : ℝ) 0 g) 1 0 ≤
        -(β * Real.log (r : ℝ))} ≤
        ENNReal.ofReal (2 * (r : ℝ) ^ (-(β ^ 2 / 2))) :=
      large_circle_average_lower_tail μ hμ r β hβ
    _ ≤ ENNReal.ofReal η :=
      ENNReal.ofReal_le_ofReal (le_of_lt (hR _ hrR))

end SupercriticalLQGUniqueness.B2.DG20Lim
