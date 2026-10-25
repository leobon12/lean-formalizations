import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Inputs
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneASource
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBRepairedLargeAnnulusGeometry

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 

theorem laneA2_cover0_to_old {Ucross Uaround E F : Set ℂ} {N : ℝ}
    (h : LaneCRepairedInputs.RectAnnulusCoverAt Ucross Uaround E F 0 0 N) :
    LaneAInputs.RectAnnulusCover Ucross Uaround E F N := h

 

theorem laneA2_repaired_large_to_old : LaneAInputs.LargeAnnulusGeometry := by
  obtain ⟨R₀, G, hR₀, hG, hR⟩ := laneB_repairedLargeAnnulusGeometry
  refine ⟨R₀, G, by linarith, hG, ?_⟩
  intro R hRR
  exact laneA2_cover0_to_old (hR R hRR)

 

theorem laneA2_large_tails {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ p Cneg cNeg Cpos cPos R₀ G : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < Cneg ∧ 0 < cNeg ∧
      0 < Cpos ∧ 0 < cPos ∧ 24 ≤ R₀ ∧ 1 ≤ G ∧
      ∀ R : ℝ, R₀ ≤ R →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W),
          ∀ (m : ℕ) (T : ℝ), 3 < T →
            P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
              {z : ℂ | dist z 0 ∈ Icc R (2 * R)}
              (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R)) <
              ENNReal.ofReal (T⁻¹ * ellN ξ W P m (ENNReal.ofReal p))} ≤
              ENNReal.ofReal ((G * Cneg) * R *
                Real.exp (-cNeg * (Real.log T)^2)) ∧
            P {ω | ENNReal.ofReal ((T * R) *
              (LambdaN ξ W P m (ENNReal.ofReal p) *
                ellN ξ W P m (ENNReal.ofReal p))) <
              (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
                ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
                {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R}
                (sphere (0 : ℂ) R) (sphere (0 : ℂ) (2 * R))} ≤
              ENNReal.ofReal (laneA_upperConstant G Cpos cPos * R *
                Real.exp (-(cPos / 4) * (Real.log T)^2 /
                  Real.log (Real.log T))) := by
  obtain ⟨R₀, G, hR₀, hG, hR⟩ := laneB_repairedLargeAnnulusGeometry
  obtain ⟨p, Cneg, cNeg, Cpos, cPos, hp, hpHalf, hCn, hcn,
    hCp, hcp, htail⟩ := laneA_unit_rectangle_tails hξ
  refine ⟨p, Cneg, cNeg, Cpos, cPos, R₀, G,
    hp, hpHalf, hCn, hcn, hCp, hcp, hR₀, hG, ?_⟩
  intro R hRR Ω _ P W hW m T hT
  obtain ⟨hlow, hupp⟩ := htail P W hW
  exact laneA_source_tails_of_cover P hW (by linarith [hR₀, hRR]) hG
    (laneA2_cover0_to_old (hR R hRR)) hCp hcp hlow hupp m T hT

end SupercriticalLQGUniqueness.B2.DG20Conc
