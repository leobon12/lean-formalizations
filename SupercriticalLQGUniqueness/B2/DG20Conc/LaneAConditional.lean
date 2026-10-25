import SupercriticalLQGUniqueness.B2.DG20Conc.LaneAAssembly

 









set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u v

 

theorem laneA_annulus_tails_of_inputs {ι : Type v}
    {Ucross Uaround E F : ι → Set ℂ}
    (hlarge : LaneAInputs.LargeAnnulusGeometry)
    (hsmall : LaneAInputs.UnitBlockGeometry Ucross Uaround E F)
    {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Cneg cNeg Cpos cPos R₀ Glarge Gsmall : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < Cneg ∧ 0 < cNeg ∧
      0 < Cpos ∧ 0 < cPos ∧ 1 ≤ R₀ ∧ 1 ≤ Glarge ∧ 1 ≤ Gsmall ∧
      (∀ R : ℝ, R₀ ≤ R →
        ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W),
          ∀ (m : ℕ) (T : ℝ), 3 < T →
            P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
              {z : ℂ | dist z 0 ∈ Icc R (2 * R)}
              (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) <
              ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
              ENNReal.ofReal (Glarge * R) * ENNReal.ofReal
                (Cneg * Real.exp (-cNeg * (Real.log T)^2)) ∧
            P {ω | ENNReal.ofReal ((Glarge * R) *
              (T * LambdaN ξ W P m (ENNReal.ofReal p) *
                ellN ξ W P m (ENNReal.ofReal p))) <
              (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
                ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
                {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
                (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R))} ≤
              ENNReal.ofReal (Glarge * R) * ENNReal.ofReal
                (Cpos * Real.exp (-cPos * (Real.log T)^2 /
                  Real.log (Real.log T)))) ∧
      (∀ i : ι, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W),
          ∀ (m : ℕ) (T : ℝ), 3 < T →
            P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
              (Ucross i) (E i) (F i) <
              ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
              ENNReal.ofReal Gsmall * ENNReal.ofReal
                (Cneg * Real.exp (-cNeg * (Real.log T)^2)) ∧
            P {ω | ENNReal.ofReal (Gsmall *
              (T * LambdaN ξ W P m (ENNReal.ofReal p) *
                ellN ξ W P m (ENNReal.ofReal p))) <
              (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
                ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
                (Uaround i) (E i) (F i)} ≤
              ENNReal.ofReal Gsmall * ENNReal.ofReal
                (Cpos * Real.exp (-cPos * (Real.log T)^2 /
                  Real.log (Real.log T)))) := by
  obtain ⟨R₀, Glarge, hR₀, hGlarge, hlargeR⟩ := hlarge
  obtain ⟨Gsmall, hGsmall, hsmallI⟩ := hsmall
  obtain ⟨p, Cneg, cNeg, Cpos, cPos, hp, hpHalf, hCneg, hcNeg,
    hCpos, hcPos, htail⟩ := laneA_unit_rectangle_tails hξ
  refine ⟨p, Cneg, cNeg, Cpos, cPos, R₀, Glarge, Gsmall,
    hp, hpHalf, hCneg, hcNeg, hCpos, hcPos, hR₀, hGlarge, hGsmall, ?_, ?_⟩
  · intro R hR Ω inst P W hW m T hT
    obtain ⟨hlow, hupp⟩ := htail P W hW
    exact laneA_annulus_tails_of_cover hW (hlargeR R hR) hlow hupp m T hT
  · intro i Ω inst P W hW m T hT
    obtain ⟨hlow, hupp⟩ := htail P W hW
    exact laneA_annulus_tails_of_cover hW (hsmallI i) hlow hupp m T hT

end SupercriticalLQGUniqueness.B2.DG20Conc
