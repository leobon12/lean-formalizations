import HigherDimLQGMetric.B3.Interfaces
import HigherDimLFPP.Exist.Quantile

/-!
# Lower-median bookkeeping for the LFPP normalization

The frozen normalization `aEps` is the lower median of a point-to-point LFPP
distance under `normLGFLaw`.  These elementary bridges let later arguments use
the existing quantile API without altering that definition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- The lower median defined using preimages agrees with the lower quantile of
the push-forward law when the random variable is a.e. measurable. -/
theorem l6a_lowerMedian_eq_lowerQuantile_map {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) (hX : AEMeasurable X μ) :
    lowerMedian μ X = LQGMetric.lowerQuantile (μ.map X) 2⁻¹ := by
  unfold lowerMedian LQGMetric.lowerQuantile
  congr 1
  ext m
  change ((2 : ℝ≥0∞)⁻¹ ≤ μ {x | X x ≤ m}) ↔
    ((2 : ℝ≥0∞)⁻¹ ≤ (μ.map X) (Set.Iic m))
  rw [Measure.map_apply_of_aemeasurable hX measurableSet_Iic]
  rfl

/-- An almost-surely positive random variable has a positive lower median. -/
theorem l6a_lowerMedian_pos {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (X : α → ℝ)
    (hX : AEMeasurable X μ) (hpos : ∀ᵐ x ∂μ, 0 < X x) :
    0 < lowerMedian μ X := by
  rw [l6a_lowerMedian_eq_lowerQuantile_map μ X hX]
  exact HigherDimLFPP.Conc.lowerQuantile_map_pos hX hpos
    (by norm_num : (0 : ℝ≥0∞) < 2⁻¹)
    (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)

/-- The fixed LFPP normalizer is literally the lower median under the
normalized LGF law. -/
theorem l6a_aEps_eq_lowerMedian {d : ℕ} (κ : Rd d → ℝ) (ξ ε : ℝ) :
    aEps κ ξ ε = lowerMedian (normLGFLaw d)
      (fun h => lfppDist κ ξ ε h (0, e₁ d)) := rfl

end HigherDimLQGMetric
