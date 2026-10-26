import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import LQGMetric.Papers.DFGPS.L2_2

/-!
# Compact-uniform logarithmic bounds for circle averages

DFGPS Lemma 2.2 gives a global circle-average bound with the small-scale logarithm and the
large-scale power `1/2 + ζ`.  At `ζ = 1/2`, this specializes to a logarithmic bound at both ends.
This file converts it to the `1 + |log s|` form used in §2.1 of the manuscript.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open LQGMetric (DistC)
open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF)

namespace SupercriticalLFPPAS.Field

/-- A jointly continuous circle-average version of a normalized whole-plane GFF obeys the
compact-uniform logarithmic bound from Lemma 2.1.  The random constant is finite because it is a
real-valued witness on the almost-sure event. -/
theorem exists_circleAverage_log_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGMetric.DFGPS.IsCircleAvgVersion h P H ∧
      ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s → ∀ z ∈ K,
        |H s z ω| ≤ C * (1 + |Real.log s|) := by
  obtain ⟨H, hH⟩ := LQGMetric.DFGPS.exists_isCircleAvgVersion hh.1
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  obtain ⟨A, hA, hAb⟩ := LQGMetric.DFGPS.lem2_2 hh.1 hH R
  have hBound := hAb (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  refine ⟨H, hH, ?_⟩
  filter_upwards [hBound] with ω hω
  obtain ⟨C, hC⟩ := hω
  refine ⟨|C| * max A 1, by positivity, fun s hs z hz => ?_⟩
  have ht : 0 ≤ |Real.log s| := abs_nonneg _
  have hA0 : 0 ≤ A := le_of_lt hA
  have hB0 : 0 ≤ max A 1 := le_trans (le_of_lt one_pos) (le_max_right _ _)
  have hBA : A ≤ max A 1 := le_max_left _ _
  have hB1 : 1 ≤ max A 1 := le_max_right _ _
  have hlog : Real.log (1 / s) = -Real.log s := by
    rw [one_div, Real.log_inv]
  have hpow : Real.log s ^ (1 / 2 + 1 / 2 : ℝ) = Real.log s := by
    rw [show (1 / 2 + 1 / 2 : ℝ) = 1 by norm_num, Real.rpow_one]
  have hfirst : A * Real.log (1 / s) ≤ max A 1 * |Real.log s| := by
    rw [hlog]
    calc A * (-Real.log s) ≤ A * |Real.log s| :=
          mul_le_mul_of_nonneg_left (neg_le_abs _) hA0
      _ ≤ max A 1 * |Real.log s| :=
          mul_le_mul_of_nonneg_right hBA ht
  have hsecond : Real.log s ^ (1 / 2 + 1 / 2 : ℝ) ≤ max A 1 * |Real.log s| := by
    rw [hpow]
    calc Real.log s ≤ |Real.log s| := le_abs_self _
      _ ≤ max A 1 * |Real.log s| := le_mul_of_one_le_left ht hB1
  have hthird : (1 : ℝ) ≤ max A 1 * (1 + |Real.log s|) := by
    calc (1 : ℝ) ≤ max A 1 := hB1
      _ ≤ max A 1 * (1 + |Real.log s|) := by
        exact le_mul_of_one_le_right hB0 (by linarith)
  have hM :
      max (max (A * Real.log (1 / s)) (Real.log s ^ (1 / 2 + 1 / 2 : ℝ))) 1 ≤
        max A 1 * (1 + |Real.log s|) := by
    apply max_le
    · apply max_le
      · exact hfirst.trans (by nlinarith [hB0, ht])
      · exact hsecond.trans (by nlinarith [hB0, ht])
    · exact hthird
  have hM0 : 0 ≤ max (max (A * Real.log (1 / s))
      (Real.log s ^ (1 / 2 + 1 / 2 : ℝ))) 1 := by
    exact le_trans (by norm_num) (le_max_right _ _)
  calc
    |H s z ω| ≤ C * max (max (A * Real.log (1 / s))
        (Real.log s ^ (1 / 2 + 1 / 2 : ℝ))) 1 := hC s hs z (hR hz)
    _ ≤ |C| * max (max (A * Real.log (1 / s))
        (Real.log s ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hM0
    _ ≤ |C| * (max A 1 * (1 + |Real.log s|)) :=
      mul_le_mul_of_nonneg_left hM (abs_nonneg C)
    _ = (|C| * max A 1) * (1 + |Real.log s|) := by ring

end SupercriticalLFPPAS.Field
