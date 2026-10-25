import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Inputs
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem laneA3_log_resampling_le
    {L Lcopy A : ℝ} (hL : 0 < L) (hLcopy : 0 < Lcopy)
    (hcopy : Lcopy ≤ L + A) :
    Real.log Lcopy - Real.log L ≤ A / L := by
  calc
    Real.log Lcopy - Real.log L = Real.log (Lcopy / L) := by
      rw [Real.log_div hLcopy.ne' hL.ne']
    _ ≤ Lcopy / L - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hLcopy hL)
    _ ≤ A / L := by
      have hfrac : Lcopy / L ≤ 1 + A / L := by
        apply (div_le_iff₀ hL).mpr
        rw [add_mul, one_mul, div_mul_cancel₀ _ hL.ne']
        exact hcopy
      linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
