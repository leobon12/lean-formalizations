import SupercriticalLQGUniqueness.B2.DG20Conc.J1BlockAroundScale

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_same_p_physical_small_high
    {ξ : ℝ} (hξ : 0 < ξ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ p A CN cN CP cP : ℝ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < A ∧
      0 < CN ∧ 0 < cN ∧ 0 < CP ∧ 0 < cP ∧
      LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : 64 ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ)
        (hT : Real.exp ((A + 5) * (C + 1) *
          Real.sqrt ((K : ℝ) + 1)) ≤ T),
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
    hp, hpHalf, hA, hCN, hcN, hCP, hcP, hunit, htail⟩ :=
      j1_same_p_scaled_upper_union hξ C hC
  refine ⟨p, A, CN, cN, CP, cP,
    hp, hpHalf, hA, hCN, hcN, hCP, hcP, hunit, ?_⟩
  intro Ω _ P W hW K n hK hKn hH i T hT
  obtain ⟨hlow, hupp⟩ := htail P W hW K n hK hKn hH i T hT
  refine ⟨hlow, ?_⟩
  have hr : 0 < (2 : ℝ)⁻¹ ^ K := by positivity
  have hr0 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hr).ne'
  have hrt : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ K) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  apply (measure_mono ?_).trans hupp
  rintro ω ⟨b, hb, hbad⟩
  refine ⟨b, hb, ?_⟩
  have hle := j1_block_around_le P W hW hKn ξ i
    (T20.dyCenter K b) ω
  exact (ENNReal.mul_lt_mul_iff_right hr0 hrt).mp
    (hbad.trans_le hle)

end SupercriticalLQGUniqueness.B2.DG20Conc
