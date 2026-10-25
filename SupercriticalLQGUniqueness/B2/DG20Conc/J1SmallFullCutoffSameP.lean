import SupercriticalLQGUniqueness.B2.DG20Conc.J1SmallSourceCutoffOfFull
import SupercriticalLQGUniqueness.B2.DG20Conc.J1HalfStartMono

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_small_full_half_and_cutoff_same_p
    {ξ : ℝ} (hξ : 0 < ξ) (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ p CN cN CP cP : ℝ, ∃ Kfull : ℕ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < CN ∧ 0 < cN ∧
      0 < CP ∧ 0 < cP ∧ 64 ≤ Kfull ∧
      LaneA2HasUnitTails.{u} ξ p ∧
      (∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : Kfull ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ)
        (hT : (2 : ℝ)^(((1 / 2 : ℝ) * (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀))) < T),
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        P {ω | ∃ b ∈ I, ω ∈ j1SmallFullLowerEvent ξ W P K n i T L b} ≤
          ENNReal.ofReal (CN * (5 : ℝ)^K * Real.exp
            (-cN * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1SmallFullUpperEvent ξ W P hW K n i T L b} ≤
          ENNReal.ofReal (CP * (5 : ℝ)^K * Real.exp
            (-cP * (Real.log T)^2 /
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))))) ∧
      ∃ CN' cN' CP' cP' : ℝ, ∃ Kcut : ℕ,
        0 < CN' ∧ 0 < cN' ∧ 0 < CP' ∧ 0 < cP' ∧ 64 ≤ Kcut ∧
        ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : Kcut ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ)
        (hT : (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T),
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        P {ω | ∃ b ∈ I, ω ∈ j1SmallCutLowerEvent ξ Q W P K n i T L b} ≤
          ENNReal.ofReal (CN' * (5 : ℝ)^K * Real.exp
            (-cN' * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1SmallCutUpperEvent ξ Q W P hW K n i T L b} ≤
          ENNReal.ofReal (CP' * (5 : ℝ)^K * Real.exp
            (-cP' * (Real.log T)^2 /
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))) := by
  obtain ⟨p, CN, cN, CP, cP, Kfull,
    hp, hpHalf, hCN, hcN, hCP, hcP, hKfull, hunit, hfull⟩ :=
    j1_small_source_full_tails_half hξ Q hε C hC
  obtain ⟨CN', cN', CP', cP', Kcut,
    hCN', hcN', hCP', hcP', hKcut, hcut⟩ :=
    j1_small_source_cutoff_tails_of_full hξ Q hε C hC Kfull
      hCN hcN hCP hcP hKfull hfull
  exact ⟨p, CN, cN, CP, cP, Kfull, hp, hpHalf,
    hCN, hcN, hCP, hcP, hKfull, hunit, hfull,
    CN', cN', CP', cP', Kcut,
    hCN', hcN', hCP', hcP', hKcut, hcut⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
