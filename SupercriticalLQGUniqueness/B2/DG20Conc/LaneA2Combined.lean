import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2LargeSameP

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem laneA2_same_index_annuli_of_C1
    (hC1 : LaneBInputs.C1UnitBlockGeometry)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Aneg Apos G Cneg cNeg Cpos cPos CU cU : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 1 ≤ Aneg ∧ 1 ≤ Apos ∧ 1 ≤ G ∧
      0 < Cneg ∧ 0 < cNeg ∧ 0 < Cpos ∧ 0 < cPos ∧
      0 < CU ∧ 0 < cU ∧
      (∃ R₀ Glarge CLneg cLneg CLpos cLpos : ℝ,
        24 ≤ R₀ ∧ 1 ≤ Glarge ∧ 0 < CLneg ∧ 0 < cLneg ∧
        0 < CLpos ∧ 0 < cLpos ∧
        ∀ (R : ℝ), R₀ ≤ R →
          ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
            (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
            (m : ℕ) (T : ℝ), 3 < T →
              P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
                {z : ℂ | dist z 0 ∈ Set.Icc R (2 * R)}
                (Metric.sphere (0 : ℂ) R) (Metric.sphere (0 : ℂ) (2 * R)) <
                ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
                ENNReal.ofReal ((Glarge * CLneg) * R *
                  Real.exp (-cLneg * (Real.log T)^2)) ∧
              P {ω | ENNReal.ofReal ((T * R) *
                (LambdaN ξ W P m (ENNReal.ofReal p) *
                  ellN ξ W P m (ENNReal.ofReal p))) <
                (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
                  ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
                  {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
                  (Metric.sphere (0 : ℂ) R)
                  (Metric.sphere (0 : ℂ) (2 * R))} ≤
                ENNReal.ofReal (laneA_upperConstant Glarge CLpos cLpos * R *
                  Real.exp (-(cLpos / 4) * (Real.log T)^2 /
                    Real.log (Real.log T)))) ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
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
                Real.log (Real.log T)))) := by
  obtain ⟨p, Aneg, Apos, G, Cneg, cNeg, Cpos, cPos, CU, cU,
    hp, hpHalf, hAn, hAp, hG, hCn, hcn, hCp, hcp, hCU, hcU,
    hunit, hsmall⟩ := laneA2_small_source_of_C1 hC1 hξ
  obtain ⟨R₀, Glarge, CLneg, cLneg, CLpos, cLpos,
    hR₀, hGL, hCLn, hcLn, hCLp, hcLp, hlarge⟩ :=
      laneA2_large_same_p hunit
  exact ⟨p, Aneg, Apos, G, Cneg, cNeg, Cpos, cPos, CU, cU,
    hp, hpHalf, hAn, hAp, hG, hCn, hcn, hCp, hcp, hCU, hcU,
    ⟨R₀, Glarge, CLneg, cLneg, CLpos, cLpos,
      hR₀, hGL, hCLn, hcLn, hCLp, hcLp, hlarge⟩, hsmall⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
