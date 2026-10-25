import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2ShiftRates

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem laneA2_small_source_of_C1
    (hC1 : LaneBInputs.C1UnitBlockGeometry)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Aneg Apos G Cneg cNeg Cpos cPos CU cU : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 1 ≤ Aneg ∧ 1 ≤ Apos ∧ 1 ≤ G ∧
      0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      0 < CU ∧ 0 < cU ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (m : ℕ) (B : ℝ) (hB : 1 ≤ B)
        (hΛ : LambdaN ξ W P m (ENNReal.ofReal p) ≤ B)
        (T : ℝ)
        (hTL : max (3 * (Aneg * B^4)) ((Aneg * B^4)^2) < T)
        (hTU : max (3 * (G * Apos)) ((G * Apos)^2) < T)
        (i : Bool),
        P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
          (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
          ENNReal.ofReal (T⁻¹ *
            ellN ξ W P m (ENNReal.ofReal p))} ≤
          ENNReal.ofReal G * ENNReal.ofReal
            (Cneg * Real.exp (-(cNeg / 4) * (Real.log T)^2)) ∧
        P {ω | ENNReal.ofReal (T *
            LambdaN ξ W P m (ENNReal.ofReal p) *
              ellN ξ W P m (ENNReal.ofReal p)) <
          (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)} ≤
          ENNReal.ofReal G * ENNReal.ofReal
            ((Cpos + CU) * Real.exp
              (-(min cPos cU / 4) * (Real.log T)^2 /
                Real.log (Real.log T))) := by
  obtain ⟨p, Aneg, Apos, G, Cneg, cNeg, Cpos, cPos, CU, cU,
    hp, hpHalf, hAn, hAp, hG, hCn, hcn, hCp, hcp, hCU, hcU, hunit, hparam⟩ :=
      laneA2_small_param_of_C1 hC1 hξ
  refine ⟨p, Aneg, Apos, G, Cneg, cNeg, Cpos, cPos, CU, cU,
    hp, hpHalf, hAn, hAp, hG, hCn, hcn, hCp, hcp, hCU, hcU,
    hunit, ?_⟩
  intro Ω _ P W hW m B hB hΛ T hTL hTU i
  have hG0 : 0 < G := by linarith
  have hAp0 : 0 < Apos := by linarith
  have hAn0 : 0 < Aneg := by linarith
  have hB0 : 0 < B := by linarith
  have hB4 : 1 ≤ B^4 := one_le_pow₀ hB
  have hDL : 1 ≤ Aneg * B^4 := by nlinarith
  have hDU : 1 ≤ G * Apos := by nlinarith
  have hGDU : G ≤ G * Apos := by nlinarith
  have hTUG : max (3 * G) (G^2) < T := by
    have h3 : 3 * G ≤ 3 * (G * Apos) := by nlinarith
    have hsq : G^2 ≤ (G * Apos)^2 := by nlinarith [sq_nonneg (G * Apos - G)]
    exact max_lt (h3.trans_lt ((le_max_left _ _).trans_lt hTU))
      (hsq.trans_lt ((le_max_right _ _).trans_lt hTU))
  let sL : ℝ := T / (Aneg * B^4)
  let sU : ℝ := T / (G * Apos)
  have hsL : 3 < sL := (laneA2_shifted_sq_rate hDL hTL).1
  have hsU : 3 < sU := (laneA2_shifted_sq_rate hDU hTU).1
  obtain ⟨hlow, hupp⟩ := hparam P W hW m B hB hΛ sL sU hsL hsU i
  have hcancelL : Aneg * B^4 * sL = T := by
    dsimp [sL]
    exact laneA2_lower_param_cancel hAn0 hB0
  have hcancelU : G * (Apos * sU *
      LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p)) =
      T * LambdaN ξ W P m (ENNReal.ofReal p) *
        ellN ξ W P m (ENNReal.ofReal p) := by
    dsimp [sU]
    field_simp
  rw [hcancelL] at hlow
  rw [hcancelU] at hupp
  have hqlo : Cneg * Real.exp (-cNeg * (Real.log sL)^2) ≤
      Cneg * Real.exp (-(cNeg / 4) * (Real.log T)^2) :=
    laneA2_shifted_lower_tail_rate hDL hTL hCn.le hcn
  have harg : Apos * sU = T / G := by
    dsimp [sU]
    exact laneA2_upper_param_arg hG0 hAp0
  have hqhi : Cpos * Real.exp
        (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) +
      CU * Real.exp
        (-cU * (Real.log (Apos * sU))^2 /
          Real.log (Real.log (Apos * sU))) ≤
      (Cpos + CU) * Real.exp
        (-(min cPos cU / 4) * (Real.log T)^2 /
          Real.log (Real.log T)) := by
    rw [harg]
    exact laneA2_shifted_upper_tail_rate hDU hG hTU hTUG
      hCp.le hCU.le hcp hcU
  constructor
  · exact hlow.trans (mul_le_mul_of_nonneg_left
      (ENNReal.ofReal_le_ofReal hqlo) (zero_le : (0 : ℝ≥0∞) ≤ _))
  · exact hupp.trans (mul_le_mul_of_nonneg_left
      (ENNReal.ofReal_le_ofReal hqhi) (zero_le : (0 : ℝ≥0∞) ≤ _))

end SupercriticalLQGUniqueness.B2.DG20Conc
