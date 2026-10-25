import SupercriticalLQGUniqueness.B2.DG20Conc.J1SamePPhysicalSmall
import SupercriticalLQGUniqueness.B2.DG20Conc.J1CrossRange
import SupercriticalLQGUniqueness.B2.DG20Conc.J1UpperRange

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_same_p_physical_small_all
    {ξ : ℝ} (hξ : 0 < ξ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ p CN cN CP cP : ℝ,
      0 < p ∧ p < 2⁻¹ ∧
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : 64 ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ) (hT : 3 < T),
        P {ω | ∃ b ∈ T20B.nearIdx K,
          crossLenIn ξ (fun z => phiMN W P K n z ω)
            (laneBBlockAnnulus i (T20.dyCenter K b) K)
            (j1BlockInner i (T20.dyCenter K b) K)
            (j1BlockOuter i (T20.dyCenter K b) K) <
            ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CN * Real.exp (-cN * (Real.log T)^2)) ∧
        P {ω | ∃ b ∈ T20B.nearIdx K,
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
            ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
            (lfppContMetric ξ (fun z => phiMN W P K n z ω)
              ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
              (laneBBlockAround i (T20.dyCenter K b) K)
              (j1BlockInner i (T20.dyCenter K b) K)
              (j1BlockOuter i (T20.dyCenter K b) K)} ≤
          ENNReal.ofReal ((5 : ℝ)^K) *
            ENNReal.ofReal (CP * Real.exp
              (-cP * (Real.log T)^2 / Real.log (Real.log T))) := by
  obtain ⟨p, A, CN, cN, CP, cP,
    hp, hpHalf, hA, hCN, hcN, hCP, hcP, hunit, hhigh⟩ :=
      j1_same_p_physical_small_high hξ C hC
  let D : ℝ := (A + 5) * (C + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨CN', cN', hCN', hcN', hlowExt⟩ :=
    j1_cross_range_extension (A + 5) C CN cN
      (by linarith) hC hCN hcN
  obtain ⟨CP', cP', hCP', hcP', huppExt⟩ :=
    j1_upper_range_extension D CP cP hD hCP hcP
  refine ⟨p, CN', cN', CP', cP', hp, hpHalf,
    hCN', hcN', hCP', hcP', hunit, ?_⟩
  intro Ω _ P W hW K n hK hKn hH i T hT
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let Es : Set Ω := {ω | ∃ b ∈ T20B.nearIdx K,
    crossLenIn ξ (fun z => phiMN W P K n z ω)
      (laneBBlockAnnulus i (T20.dyCenter K b) K)
      (j1BlockInner i (T20.dyCenter K b) K)
      (j1BlockOuter i (T20.dyCenter K b) K) <
      ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P (n - K))}
  let Ea : Set Ω := {ω | ∃ b ∈ T20B.nearIdx K,
    ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) *
      ENNReal.ofReal (T * lambdaN ξ W P (n - K)) <
      (lfppContMetric ξ (fun z => phiMN W P K n z ω)
        ((isPhiVersion_phiMN hW hKn).cont ω)).aroundDist
        (laneBBlockAround i (T20.dyCenter K b) K)
        (j1BlockInner i (T20.dyCenter K b) K)
        (j1BlockOuter i (T20.dyCenter K b) K)}
  have hs : P Es ≤ ENNReal.ofReal ((5 : ℝ)^K) *
      ENNReal.ofReal (CN' * Real.exp (-cN' * (Real.log T)^2)) := by
    apply hlowExt P K hK T hT Es
    intro ht
    exact (hhigh P W hW K n hK hKn hH i T ht).1
  have ha : P Ea ≤ ENNReal.ofReal ((5 : ℝ)^K) *
      ENNReal.ofReal (CP' * Real.exp
        (-cP' * (Real.log T)^2 / Real.log (Real.log T))) := by
    apply huppExt P K hK T hT Ea
    intro ht
    exact (hhigh P W hW K n hK hKn hH i T
      (show Real.exp (D * Real.sqrt ((K : ℝ) + 1)) ≤ T from ht)).2
  exact ⟨hs, ha⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
