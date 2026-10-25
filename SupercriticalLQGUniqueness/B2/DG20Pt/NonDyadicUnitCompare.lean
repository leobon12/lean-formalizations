import SupercriticalLQGUniqueness.B2.DG20Pt.NonDyadicLowBandGaussian

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem dg20_non_dyadic_unit_square_compare
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (n : ℕ) (s u : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hu : 0 ≤ u) :
    let r : ℝ := (2 : ℝ) ^ s
    let W' := dg20ScaledNoise r (by positivity : 0 < r) W
    P.real {ω | ferniqueCF * Real.sqrt 6 + u ≤
      ⨆ v : ferniqueBox 0 1,
        |phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 v ω -
          phiMN W P 0 n ((r : ℂ) * v) ω|} ≤
      2 * Real.exp (-u ^ 2 / (2 * Real.log 2)) := by
  dsimp only
  let r : ℝ := (2 : ℝ) ^ s
  have hr : 0 < r := by dsimp [r]; positivity
  let W' := dg20ScaledNoise r hr W
  obtain ⟨hW', hdiff⟩ := dg20_non_dyadic_field_difference_coupled P W hW n s hs.le
  have hevent :
      {ω | ferniqueCF * Real.sqrt 6 + u ≤
        ⨆ v : ferniqueBox 0 1,
          |phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 v ω -
            phiMN W P 0 n ((r : ℂ) * v) ω|} =ᵐ[P]
      {ω | ferniqueCF * Real.sqrt 6 + u ≤
        ⨆ v : ferniqueBox 0 1,
          |phiVer W' P ((2 : ℝ) ^ (-s)) 1 v ω|} := by
    filter_upwards [hdiff] with ω hω
    have heq : (⨆ v : ferniqueBox 0 1,
        |phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 v ω -
          phiMN W P 0 n ((r : ℂ) * v) ω|) =
        ⨆ v : ferniqueBox 0 1,
          |phiVer W' P ((2 : ℝ) ^ (-s)) 1 v ω| := by
      apply iSup_congr
      intro v
      rw [hω v]
    exact heq ▸ rfl
  have htail := dg20_low_band_unit_square_gaussian P W' hW' s u hs hs1 hu
  have hrealeq : P.real {ω | ferniqueCF * Real.sqrt 6 + u ≤
      ⨆ v : ferniqueBox 0 1,
        |phiVer W' P ((2 : ℝ) ^ (-((n : ℝ) + s))) 1 v ω -
          phiMN W P 0 n ((r : ℂ) * v) ω|} =
      P.real {ω | ferniqueCF * Real.sqrt 6 + u ≤
        ⨆ v : ferniqueBox 0 1,
          |phiVer W' P ((2 : ℝ) ^ (-s)) 1 v ω|} := by
    simpa only [Measure.real] using congrArg ENNReal.toReal (measure_congr hevent)
  exact hrealeq.trans_le htail

end SupercriticalLQGUniqueness.B2.DG20Pt
