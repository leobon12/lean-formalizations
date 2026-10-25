import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2SmallFull
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LargeSameP
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCUnitGeometry

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem laneA2_small_induction
    {ξ : ℝ} (hξ : 0 < ξ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ p A₀ CN cN CP cP : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < A₀ ∧
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K m : ℕ)
        (hH : LambdaN ξ W P m (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ) (hT : 3 < T),
        (Real.exp (A₀ * (C + 1) * Real.sqrt ((K : ℝ) + 1)) ≤ T →
          P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
            (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
            ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2))) ∧
        P {ω | ENNReal.ofReal (T *
          LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p)) <
          (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)} ≤
          ENNReal.ofReal (CP * Real.exp
            (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
  exact laneA2_small_induction_of_C1 laneC_unit_block_geometry hξ C hC

end SupercriticalLQGUniqueness.B2.DG20Conc
