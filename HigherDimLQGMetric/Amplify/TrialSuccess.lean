import HigherDimLQGMetric.Amplify.TrialProb

/-! Convert the full-field witness probability into a fine-trial success bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory
open scoped ENNReal

variable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P]

/-- Losing at most half the witness probability to coarse oscillation leaves
each fine trial with success probability at least `pstar/2`. -/
theorem amplify_trial_success_le_compl
    (W E B : Set Ω) (hE : NullMeasurableSet E P)
    {pstar η : ℝ} (hpstar : 0 < pstar)
    (hηsmall : η ≤ pstar / 2)
    (hW : ENNReal.ofReal pstar ≤ P W)
    (htransfer : P W ≤ P E + P B)
    (hB : P B ≤ ENNReal.ofReal η) :
    ENNReal.ofReal (pstar / 2) ≤ P E ∧
      P Eᶜ ≤ ENNReal.ofReal (1 - pstar / 2) := by
  have hp2 : 0 ≤ pstar / 2 := by linarith
  have hP : ENNReal.ofReal pstar =
      ENNReal.ofReal (pstar / 2) + ENNReal.ofReal (pstar / 2) := by
    rw [← ENNReal.ofReal_add hp2 hp2]
    congr 1
    ring
  have hsum : ENNReal.ofReal (pstar / 2) + ENNReal.ofReal (pstar / 2) ≤
      P E + ENNReal.ofReal (pstar / 2) := by
    calc
      _ = ENNReal.ofReal pstar := hP.symm
      _ ≤ P W := hW
      _ ≤ P E + P B := htransfer
      _ ≤ P E + ENNReal.ofReal η := by gcongr
      _ ≤ P E + ENNReal.ofReal (pstar / 2) := by
        gcongr
  have hsuccess : ENNReal.ofReal (pstar / 2) ≤ P E :=
    (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 hsum
  have hfail : P Eᶜ ≤ ENNReal.ofReal (1 - pstar / 2) := by
    rw [measure_compl₀ hE (measure_ne_top P E), measure_univ]
    calc
      1 - P E ≤ 1 - ENNReal.ofReal (pstar / 2) :=
        tsub_le_tsub_left hsuccess 1
      _ = ENNReal.ofReal (1 - pstar / 2) := by
        rw [ENNReal.ofReal_sub 1 hp2]
        norm_num
  exact ⟨hsuccess, hfail⟩

end HigherDimLQGMetric
