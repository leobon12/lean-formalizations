import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.DGZ.CompareCor52

/-!
# Quantile bookkeeping for the crude band comparison

This file records the probability-to-quantile step of Appendix A's CRUDE estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric HigherDimLFPP

/-- A bad-ratio estimate transfers a lower quantile across two random distances. -/
theorem crude_quantile_of_bad_ratio {d : ℕ} {κ : Rd d → ℝ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}
    {H : ℕ → Rd d → Ω → ℝ} (hH : DGZ.IsDyadicRealization κ P W H)
    (ξ : ℝ) (n k : ℕ) {q q' : ℝ≥0∞} (hq0 : 0 < q) (hqq' : q < q')
    (hq'1 : q' < 1) {C : ℝ} (hC : 0 ≤ C)
    (hbad : P {ω | C * lfppDistance d ξ (fun z => H k z ω) <
        lfppDistance d ξ (fun z => H n z ω)} ≤ q' - q) :
    DGZ.aQ P H ξ n q ≤ C * DGZ.aQ P H ξ k q' := by
  have hq'0 : 0 < q' := hq0.trans hqq'
  have hcoarse : q' ≤ P {ω | lfppDistance d ξ (fun z => H k z ω) ≤
      DGZ.aQ P H ξ k q'} :=
    (DGZ.cmp_le_prob_iff_aQ_le hH ξ k hq'0 hq'1 _).2 le_rfl
  have hsub : {ω | lfppDistance d ξ (fun z => H k z ω) ≤ DGZ.aQ P H ξ k q'} ⊆
      {ω | lfppDistance d ξ (fun z => H n z ω) ≤ C * DGZ.aQ P H ξ k q'} ∪
        {ω | C * lfppDistance d ξ (fun z => H k z ω) <
          lfppDistance d ξ (fun z => H n z ω)} := by
    intro ω hω
    by_cases hb : C * lfppDistance d ξ (fun z => H k z ω) <
        lfppDistance d ξ (fun z => H n z ω)
    · exact Or.inr hb
    · exact Or.inl ((le_of_not_gt hb).trans (mul_le_mul_of_nonneg_left hω hC))
  have hlarge : q' ≤ P {ω | lfppDistance d ξ (fun z => H n z ω) ≤
      C * DGZ.aQ P H ξ k q'} + (q' - q) := by
    calc q' ≤ P {ω | lfppDistance d ξ (fun z => H k z ω) ≤ DGZ.aQ P H ξ k q'} := hcoarse
      _ ≤ P ({ω | lfppDistance d ξ (fun z => H n z ω) ≤ C * DGZ.aQ P H ξ k q'} ∪
          {ω | C * lfppDistance d ξ (fun z => H k z ω) <
            lfppDistance d ξ (fun z => H n z ω)}) := measure_mono hsub
      _ ≤ P {ω | lfppDistance d ξ (fun z => H n z ω) ≤
          C * DGZ.aQ P H ξ k q'} +
          P {ω | C * lfppDistance d ξ (fun z => H k z ω) <
            lfppDistance d ξ (fun z => H n z ω)} := measure_union_le _ _
      _ ≤ P {ω | lfppDistance d ξ (fun z => H n z ω) ≤
          C * DGZ.aQ P H ξ k q'} + (q' - q) := add_le_add_right hbad _
  have hq : q ≤ P {ω | lfppDistance d ξ (fun z => H n z ω) ≤
      C * DGZ.aQ P H ξ k q'} := by
    have hfinite : q' ≠ ⊤ := ne_top_of_lt hq'1
    calc q = q' - (q' - q) := (ENNReal.sub_sub_cancel hfinite hqq'.le).symm
      _ ≤ P {ω | lfppDistance d ξ (fun z => H n z ω) ≤
          C * DGZ.aQ P H ξ k q'} := (tsub_le_iff_right).2 hlarge
  exact (DGZ.cmp_le_prob_iff_aQ_le hH ξ n hq0 (hqq'.trans hq'1) _).1 hq

end HigherDimLQGContinuity
