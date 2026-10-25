import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2UnitLong

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem laneA2_small_param_of_C1
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
        (sL sU : ℝ) (hsL : 3 < sL) (hsU : 3 < sU) (i : Bool),
        P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
          (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
          ENNReal.ofReal ((Aneg * B^4 * sL)⁻¹ *
            ellN ξ W P m (ENNReal.ofReal p))} ≤
          ENNReal.ofReal G * ENNReal.ofReal
            (Cneg * Real.exp (-cNeg * (Real.log sL)^2)) ∧
        P {ω | ENNReal.ofReal (G *
            (Apos * sU * LambdaN ξ W P m (ENNReal.ofReal p) *
              ellN ξ W P m (ENNReal.ofReal p))) <
          (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
            ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
            (laneCUnitUaround i) (laneCUnitInner i)
            (laneCUnitOuter i)} ≤
          ENNReal.ofReal G * ENNReal.ofReal
            (Cpos * Real.exp
              (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) +
              CU * Real.exp
              (-cU * (Real.log (Apos * sU))^2 /
                Real.log (Real.log (Apos * sU)))) := by
  obtain ⟨G, hG, hgeom⟩ := hC1
  obtain ⟨p, Aneg, Apos, Cneg, cNeg, Cpos, cPos,
    hp, hpHalf, hAn, hAp, hCn, hcn, hCp, hcp, hunitEx, hrect⟩ :=
      laneA2_repaired_rectangle_tails hξ
  obtain ⟨UN, un, CU, cU, hUN, hun, hCU, hcU, hunit⟩ := hunitEx
  refine ⟨p, Aneg, Apos, G, Cneg, cNeg, Cpos, cPos, CU, cU,
    hp, hpHalf, hAn, hAp, hG, hCn, hcn, hCp, hcp, hCU, hcU,
    ⟨UN, un, CU, cU, hUN, hun, hCU, hcU, hunit⟩, ?_⟩
  intro Ω _ P W hW m B hB hΛ sL sU hsL hsU i
  let a : ℝ := (Aneg * B^4 * sL)⁻¹ * ellN ξ W P m (ENNReal.ofReal p)
  let b : ℝ := Apos * sU * LambdaN ξ W P m (ENNReal.ofReal p) *
    ellN ξ W P m (ENNReal.ofReal p)
  let qlo : ℝ := Cneg * Real.exp (-cNeg * (Real.log sL)^2)
  let qhi : ℝ := Cpos * Real.exp
      (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) +
    CU * Real.exp
      (-cU * (Real.log (Apos * sU))^2 /
        Real.log (Real.log (Apos * sU)))
  have hlow (j : Bool) (v : Circle) (z : ℂ) :
      P {ω | T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω)
        3 v z 1 3 < a} ≤ ENNReal.ofReal qlo :=
    (hrect P W hW m B hB hΛ sL hsL v z).1
  have hupp (j : Bool) (v : Circle) (z : ℂ) :
      P {ω | b < T20B.mrectLen ξ (fun x => phiMN W P 0 m x ω)
        (if j then 0 else 3) v z 3 1} ≤ ENNReal.ofReal qhi := by
    cases j
    · have h := (hrect P W hW m B hB hΛ sU hsU v z).2
      exact h.trans (ENNReal.ofReal_le_ofReal (by
        dsimp [qhi]
        have hh : 0 ≤ CU * Real.exp
            (-cU * (Real.log (Apos * sU))^2 /
              Real.log (Real.log (Apos * sU))) := by positivity
        linarith))
    · have hSU : 3 < Apos * sU := by
        have hs : 0 < sU := by linarith
        nlinarith
      have h := laneA2_unit_long_tail P hW hunit m (Apos * sU) hSU v z
      have h' : P {ω | b < T20B.mrectLen ξ
          (fun x => phiMN W P 0 m x ω) 0 v z 3 1} ≤
          ENNReal.ofReal (CU * Real.exp
            (-cU * (Real.log (Apos * sU))^2 /
              Real.log (Real.log (Apos * sU)))) := by
        simpa only [b, mul_assoc] using h
      exact h'.trans (ENNReal.ofReal_le_ofReal (by
        dsimp [qhi]
        have hh : 0 ≤ Cpos * Real.exp
            (-cPos * (Real.log sU)^2 / Real.log (Real.log sU)) := by positivity
        linarith))
  have hh := laneA2_cover_tail_of_rect_tails P hW (hgeom i)
    (fun v z => hlow i v z) (fun v z => hupp i v z)
  exact hh

end SupercriticalLQGUniqueness.B2.DG20Conc
