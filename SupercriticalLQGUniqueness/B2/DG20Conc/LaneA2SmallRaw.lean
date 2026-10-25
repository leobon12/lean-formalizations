import SupercriticalLQGUniqueness.B2.DG20Conc.LaneA2Union

 






set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

theorem laneA2_small_raw_of_C1_and_rectangle_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {ξ a b qlo qhi : ℝ} {m : ℕ}
    (hC1 : LaneBInputs.C1UnitBlockGeometry)
    (hlow : ∀ (_i : Bool) (u : Circle) (c : ℂ),
      P {ω | T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω)
        3 u c 1 3 < a} ≤ ENNReal.ofReal qlo)
    (hupp : ∀ (i : Bool) (u : Circle) (c : ℂ),
      P {ω | b < T20B.mrectLen ξ (fun z => phiMN W P 0 m z ω)
        (if i then 0 else 3) u c 3 1} ≤ ENNReal.ofReal qhi) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ i : Bool,
      P {ω | crossLenIn ξ (fun z => phiMN W P 0 m z ω)
        (laneCUnitUcross i) (laneCUnitInner i) (laneCUnitOuter i) <
        ENNReal.ofReal a} ≤ ENNReal.ofReal G * ENNReal.ofReal qlo ∧
      P {ω | ENNReal.ofReal (G * b) <
        (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
          ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist
          (laneCUnitUaround i) (laneCUnitInner i)
          (laneCUnitOuter i)} ≤
        ENNReal.ofReal G * ENNReal.ofReal qhi := by
  obtain ⟨G, hG, hgeom⟩ := hC1
  refine ⟨G, hG, ?_⟩
  intro i
  exact laneA2_cover_tail_of_rect_tails P hW (hgeom i)
    (hlow i) (hupp i)

end SupercriticalLQGUniqueness.B2.DG20Conc
