import HigherDimLQGMetric.DGZ.NondegSmallFixedExport

/-! Quantiles and crossing laws agree for all dyadic realizations of the same kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_aQ_eq_of_realizations {κ : Rd d → ℝ} {Ω Ω' : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} {H' : ℕ → Rd d → Ω' → ℝ}
    (hH : IsDyadicRealization κ P W H)
    (hH' : IsDyadicRealization κ P' W' H')
    (ξ : ℝ) (n : ℕ) (q : ℝ≥0∞) :
    aQ P H ξ n q = aQ P' H' ξ n q := by
  unfold aQ
  exact (hH.band n).lowerQuantile_lfppDistance_eq (hH'.band n)
    hH.whiteNoise hH'.whiteNoise ξ q

theorem nd_across_bad_prob_eq_of_realizations {κ : Rd d → ℝ} {Ω Ω' : Type}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} {H' : ℕ → Rd d → Ω' → ℝ}
    (hκ : IsLFPPKernel κ)
    (hH : IsDyadicRealization κ P W H)
    (hH' : IsDyadicRealization κ P' W' H')
    (ξ : ℝ) (n : ℕ) (q : ℝ≥0∞) (r δ : ℝ) :
    P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
      δ * aQ P H ξ n q} =
    P' {ω | acrossDist ξ (fun z => H' n z ω) 0 (2 * r) r ≤
      δ * aQ P' H' ξ n q} := by
  have haQ := nd_aQ_eq_of_realizations hH hH' ξ n q
  have hmap : P.map (fun ω => acrossDist ξ (fun z => H n z ω) 0 (2 * r) r) =
      P'.map (fun ω => acrossDist ξ (fun z => H' n z ω) 0 (2 * r) r) := by
    simpa only [zero_add] using
      map_acrossDist_translate_eq (hH.band n) (hH'.band n)
        hH.whiteNoise hH'.whiteNoise hκ
        (pow_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹) n)
        ξ 0 0 (2 * r) r
  have hm : Measurable (fun ω => acrossDist ξ (fun z => H n z ω) 0 (2 * r) r) :=
    measurable_acrossDist (hH.band n).continuous (hH.band n).measurable ξ 0 (2 * r) r
  have hm' : Measurable (fun ω => acrossDist ξ (fun z => H' n z ω) 0 (2 * r) r) :=
    measurable_acrossDist (hH'.band n).continuous (hH'.band n).measurable ξ 0 (2 * r) r
  rw [haQ]
  calc
    P {ω | acrossDist ξ (fun z => H n z ω) 0 (2 * r) r ≤
        δ * aQ P' H' ξ n q} =
      (P.map (fun ω => acrossDist ξ (fun z => H n z ω) 0 (2 * r) r))
        (Set.Iic (δ * aQ P' H' ξ n q)) :=
      (Measure.map_apply hm measurableSet_Iic).symm
    _ = (P'.map (fun ω => acrossDist ξ (fun z => H' n z ω) 0 (2 * r) r))
        (Set.Iic (δ * aQ P' H' ξ n q)) := by rw [hmap]
    _ = P' {ω | acrossDist ξ (fun z => H' n z ω) 0 (2 * r) r ≤
        δ * aQ P' H' ξ n q} := Measure.map_apply hm' measurableSet_Iic

end HigherDimLQGMetric.DGZ
