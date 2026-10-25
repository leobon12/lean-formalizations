import SupercriticalLQGUniqueness.B2.DG20Conc.J1CoarseThreshold

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem j1_prob_le_of_real_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (E : Set Ω) {a : ℝ}
    (h : P.real E ≤ a) :
    P E ≤ ENNReal.ofReal a := by
  have hfin : P E ≠ ∞ :=
    measure_ne_top_of_subset (Set.subset_univ _) (by simp)
  calc
    P E = ENNReal.ofReal (P E).toReal :=
      (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal a := ENNReal.ofReal_le_ofReal h

end SupercriticalLQGUniqueness.B2.DG20Conc
