import SupercriticalLQGUniqueness.B2.DG20Conc.J1RoundSourceFull
import SupercriticalLQGUniqueness.B2.DG20Conc.J1CutoffRate

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_source_full_four_tails
    {ξ : ℝ} (hξ : 0 < ξ) (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ p C₀ c₀ : ℝ, ∃ K₀ : ℕ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < C₀ ∧ 0 < c₀ ∧ 64 ≤ K₀ ∧
      LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : K₀ ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (T : ℝ)
        (hT : (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T),
        let m := laneBCoarseIndex Q K
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        (∀ i : Bool,
          P {ω | ∃ b ∈ I, ω ∈ j1SmallFullLowerEvent ξ W P K n i T L b} ≤
            ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
              (-c₀ * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
          P {ω | ∃ b ∈ I,
            ω ∈ j1SmallFullUpperEvent ξ W P hW K n i T L b} ≤
            ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
              (-c₀ * (Real.log T)^2 /
                ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T))))) ∧
        P {ω | ∃ b ∈ I, ω ∈ j1RoundFullLowerEvent ξ W P K n m T L b} ≤
          ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
            (-c₀ * (Real.log T)^2 / (K : ℝ)^(3 * Q.ε₀))) ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1RoundFullUpperEvent ξ W P hW K n m T L b} ≤
          ENNReal.ofReal (C₀ * (5 : ℝ)^K * Real.exp
            (-c₀ * (Real.log T)^2 /
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T)))) := by
  obtain ⟨p, CNs, cNs, CPs, cPs, Ks,
    hp, hpHalf, hCNs, hcNs, hCPs, hcPs, hKs,
    hunit, hsmall⟩ := j1_small_source_full_tails hξ Q hε C hC
  obtain ⟨CNr, cNr, CPr, cPr, Kr,
    hCNr, hcNr, hCPr, hcPr, hKr,
    hround⟩ := j1_round_source_full_tails hunit hp hpHalf Q hε C hC
  obtain ⟨Kf, hKf⟩ := j1_source_loglog_ge_one Q
  let K₀ := max Ks (max Kr Kf)
  let C₀ := CNs + CPs + CNr + CPr
  let c₀ := min (min cNs cPs) (min cNr cPr)
  have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
  have hc₀ : 0 < c₀ := by
    dsimp [c₀]
    exact lt_min (lt_min hcNs hcPs) (lt_min hcNr hcPr)
  refine ⟨p, C₀, c₀, K₀, hp, hpHalf, hC₀, hc₀,
    hKs.trans (le_max_left _ _), hunit, ?_⟩
  intro Ω _ P W hW K n hK hKn hH T hT
  dsimp only
  have hKsK : Ks ≤ K := (le_max_left _ _).trans hK
  have hKrK : Kr ≤ K := (le_max_left _ _).trans
    ((le_max_right Ks (max Kr Kf)).trans hK)
  have hKfK : Kf ≤ K := (le_max_right _ _).trans
    ((le_max_right Ks (max Kr Kf)).trans hK)
  have hK2 : 2 ≤ K := by omega
  have hKone : (1 : ℝ) ≤ K := by exact_mod_cast (by omega : 1 ≤ K)
  have hD : 0 < (K : ℝ)^(3 * Q.ε₀) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hll : 1 ≤ Real.log (Real.log T) := hKf K hKfK hK2 T hT
  have hDu : 0 < (K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T) :=
    mul_pos hD (by linarith)
  have hCNsC : CNs ≤ C₀ := by dsimp [C₀]; linarith
  have hCPsC : CPs ≤ C₀ := by dsimp [C₀]; linarith
  have hCNrC : CNr ≤ C₀ := by dsimp [C₀]; linarith
  have hCPrC : CPr ≤ C₀ := by dsimp [C₀]; linarith
  have hcNsC : c₀ ≤ cNs := (min_le_left _ _).trans (min_le_left _ _)
  have hcPsC : c₀ ≤ cPs := (min_le_left _ _).trans (min_le_right _ _)
  have hcNrC : c₀ ≤ cNr := (min_le_right _ _).trans (min_le_left _ _)
  have hcPrC : c₀ ≤ cPr := (min_le_right _ _).trans (min_le_right _ _)
  have hs i := hsmall P W hW K n hKsK hKn hH i T hT
  obtain ⟨hrl, hru⟩ := hround P W hW K n hKrK hKn hH T hT
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact ⟨(hs i).1.trans
      (j1_source_rate_weaken K _ T CNs cNs C₀ c₀ hD
        hCNs.le hCNsC hcNsC),
      (hs i).2.trans
      (j1_source_rate_weaken K _ T CPs cPs C₀ c₀ hDu
        hCPs.le hCPsC hcPsC)⟩
  · exact hrl.trans
      (j1_source_rate_weaken K _ T CNr cNr C₀ c₀ hD
        hCNr.le hCNrC hcNrC)
  · exact hru.trans
      (j1_source_rate_weaken K _ T CPr cPr C₀ c₀ hDu
        hCPr.le hCPrC hcPrC)

end SupercriticalLQGUniqueness.B2.DG20Conc
