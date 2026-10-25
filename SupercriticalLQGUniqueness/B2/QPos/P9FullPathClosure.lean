import SupercriticalLQGUniqueness.B2.QPos.InputsFullPath
import SupercriticalLQGUniqueness.B2.QPos.P9JointClosure

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.QPos

theorem dgff_jointComparison_of_fullPathComparison
    (hfull : Inputs.DGFFWhiteNoiseFullPathComparison) :
    Inputs.DGFFWhiteNoiseJointComparison := by
  intro ξ Ω _ P W hW
  obtain ⟨J, hJprob, hJD, hJP, hpath⟩ := hfull ξ P W hW
  refine ⟨J, hJprob, hJD, hJP, ?_⟩
  letI (n : ℕ) : IsProbabilityMeasure (J n) := hJprob n
  intro δ hδ
  apply Filter.Tendsto.squeeze' (hpath δ hδ) tendsto_const_nhds
  · filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    apply measure_mono
    rintro v ⟨N, p, hs, ht, hp, hc⟩
    exact (dgffAnnulusDistance_le_fullPathCost_four n N p hn hs ht hp
      (ξ : ℝ) v.1).trans hc
  · filter_upwards [] with n
    exact prob_le_one

theorem dgff_upper_window_of_fullPathComparison
    (hfull : Inputs.DGFFWhiteNoiseFullPathComparison)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => boxDGFF n
      {h | dgffAnnulusDistance n (ξ : ℝ) h ≤
        (2 : ℝ) ^ (((ξ : ℝ) * Q + ε) * (n : ℝ))})
      atTop (𝓝 1) :=
  dgff_upper_window_of_jointComparison
    (dgff_jointComparison_of_fullPathComparison hfull) ξ Q hQ ε hε

theorem dg20ExponentPositive_of_P5_fullPathComparison
    (hlower : Inputs.DGFFInductionLowerWindow)
    (hfull : Inputs.DGFFWhiteNoiseFullPathComparison) :
    Iface.DG20ExponentPositive :=
  dg20ExponentPositive_of_P5_jointComparison hlower
    (dgff_jointComparison_of_fullPathComparison hfull)

end SupercriticalLQGUniqueness.B2.QPos
