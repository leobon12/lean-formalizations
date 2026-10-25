import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ShiftLower

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneA2_lower_param_cancel {A B T : ℝ} (hA : 0 < A)
    (hB : 0 < B) :
    A * B^4 * (T / (A * B^4)) = T := by
  field_simp

theorem laneA2_upper_param_cancel {G A T L : ℝ}
    (hG : 0 < G) (hA : 0 < A) :
    G * (A * (T / (G * A)) * L) = T * L := by
  field_simp

theorem laneA2_upper_param_arg {G A T : ℝ}
    (hG : 0 < G) (hA : 0 < A) :
    A * (T / (G * A)) = T / G := by
  field_simp

end SupercriticalLQGUniqueness.B2.DG20Conc
