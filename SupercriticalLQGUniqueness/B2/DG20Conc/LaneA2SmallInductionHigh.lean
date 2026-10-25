import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ThresholdExp

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem laneA2_small_induction_high_of_C1
    (hC1 : LaneBInputs.C1UnitBlockGeometry)
    {ξ : ℝ} (hξ : 0 < ξ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ p A₀ CN cN CP cP : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < A₀ ∧
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K m : ℕ)
        (hH : LambdaN ξ W P m (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ)
        (hT : Real.exp (A₀ * (C + 1) * Real.sqrt ((K : ℝ) + 1)) ≤ T),
        P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
          (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
          ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
          ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) ∧
        P {ω | ENNReal.ofReal (T *
          LambdaN ξ W P m (ENNReal.ofReal p) *
          ellN ξ W P m (ENNReal.ofReal p)) <
          (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)} ≤
          ENNReal.ofReal (CP * Real.exp
            (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨p, Aneg, Apos, G, Cneg, cNeg, Cpos, cPos, CU, cU,
    hp, hpHalf, hAn, hAp, hG, hCn, hcn, hCp, hcp, hCU, hcU,
    _, hsmall⟩ := laneA2_small_source_of_C1 hC1 hξ
  obtain ⟨A₀, hA₀, hshift⟩ :=
    laneA2_induction_shift_threshold hAn hAp hG hC
  let CN := G * Cneg
  let cN := cNeg / 4
  let CP := G * (Cpos + CU)
  let cP := min cPos cU / 4
  have hCN : 0 < CN := by dsimp [CN]; positivity
  have hcN : 0 < cN := by dsimp [cN]; positivity
  have hCP : 0 < CP := by dsimp [CP]; positivity
  have hcP : 0 < cP := by dsimp [cP]; positivity
  refine ⟨p, A₀, CN, cN, CP, cP, hp, hpHalf,
    hA₀, hCN, hcN, hCP, hcP, ?_⟩
  intro Ω _ P W hW K m hH i T hT
  let B := Real.exp (C * Real.sqrt (K : ℝ))
  have hB : 1 ≤ B := Real.one_le_exp (mul_nonneg hC (Real.sqrt_nonneg _))
  obtain ⟨hTL, hTU⟩ := hshift K T hT
  obtain ⟨hlow, hupp⟩ := hsmall P W hW m B hB hH T hTL hTU i
  constructor
  · calc
      _ ≤ ENNReal.ofReal G * ENNReal.ofReal
            (Cneg * Real.exp (-(cNeg / 4) * (Real.log T)^2)) := hlow
      _ = ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) := by
        dsimp [CN, cN]
        rw [mul_assoc, ENNReal.ofReal_mul (show 0 ≤ G by linarith)]
  · calc
      _ ≤ ENNReal.ofReal G * ENNReal.ofReal
            ((Cpos + CU) * Real.exp
              (-(min cPos cU / 4) * (Real.log T)^2 /
                Real.log (Real.log T))) := hupp
      _ = ENNReal.ofReal (CP * Real.exp
            (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
        dsimp [CP, cP]
        rw [mul_assoc, ENNReal.ofReal_mul (show 0 ≤ G by linarith)]

end SupercriticalLQGUniqueness.B2.DG20Conc
