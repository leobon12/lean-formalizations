import HigherDimLQGMetric.Limits.RandomPrecompact
import Mathlib.Topology.Compactness.Compact

/-! A samplewise convergent coupled sequence has tight marginal laws. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

theorem l7a_tight_of_ae_tendsto
    {S E : Type*} [MeasurableSpace E] (Q : Measure E)
    [IsProbabilityMeasure Q]
    [TopologicalSpace S] [MeasurableSpace S] [Nonempty S]
    [OpensMeasurableSpace S] [BorelSpace S] [PolishSpace S]
    (X : ℕ → E → S) (Y : E → S)
    (hX : ∀ n, Measurable (X n))
    (hconv : ∀ᵐ e ∂Q, Tendsto (fun n => X n e) atTop (𝓝 (Y e))) :
    IsTightMeasureSet {ν : Measure S | ∃ n, ν = Q.map (X n)} := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable S
  have hc : ∀ᵐ e ∂Q, IsCompact (closure (range fun n => X n e)) := by
    filter_upwards [hconv] with e he
    have hK := he.isCompact_insert_range
    exact hK.of_isClosed_subset isClosed_closure
      (closure_minimal (subset_insert _ _) hK.isClosed)
  exact l6c_random_precompact_tight Q X hX hc

end HigherDimLQGMetric
