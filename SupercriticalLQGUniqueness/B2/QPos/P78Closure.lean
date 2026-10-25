import SupercriticalLQGUniqueness.B2.QPos.P8FullPath
import SupercriticalLQGUniqueness.B2.QPos.P9FullPathClosure

 



set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 

theorem dgff_upper_window_proved (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto (fun n : ℕ => boxDGFF n
      {h | dgffAnnulusDistance n (ξ : ℝ) h ≤
        (2 : ℝ) ^ (((ξ : ℝ) * Q + ε) * (n : ℝ))})
      Filter.atTop (nhds 1) :=
  dgff_upper_window_of_fullPathComparison P8.dgffWhiteNoiseFullPathComparison_proved ξ Q hQ ε hε

 
theorem dg20ExponentPositive_of_P5 (hlower : Inputs.DGFFInductionLowerWindow) :
    Iface.DG20ExponentPositive :=
  dg20ExponentPositive_of_P5_fullPathComparison hlower
    P8.dgffWhiteNoiseFullPathComparison_proved

end SupercriticalLQGUniqueness.B2.QPos
