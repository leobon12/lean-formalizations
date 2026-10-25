import SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceSmallCutoffTransfer
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBXbigRealUniform

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

universe u

theorem j1_small_source_cutoff_raw_tails
    {ξ : ℝ} (hξ : 0 < ξ) (Q : PsiParams) (hε : Q.ε₀ ≤ 1)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ p CN cN CP cP Cg cg : ℝ, ∃ K₀ : ℕ,
      0 < p ∧ p < 2⁻¹ ∧ 0 < CN ∧ 0 < cN ∧
      0 < CP ∧ 0 < cP ∧ 0 < Cg ∧ 0 < cg ∧
      64 ≤ K₀ ∧ LaneA2HasUnitTails.{u} ξ p ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
        (K n : ℕ) (hK : K₀ ≤ K) (hKn : K ≤ n)
        (hH : LambdaN ξ W P (n - K) (ENNReal.ofReal p) ≤
          Real.exp (C * Real.sqrt (K : ℝ)))
        (i : Bool) (T : ℝ)
        (hT : (2 : ℝ)^((K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀)) < T),
        let I := j1SourceIdx K (j1SourceRadius Q K)
        let L := lambdaN ξ W P (n - K)
        let T' := T^(1 / 2 : ℝ)
        let g := ENNReal.ofReal
          (Cg * Real.exp (-(cg * ((1 / (2 * ξ) : ℝ) * Real.log T)^2)))
        P {ω | ∃ b ∈ I, ω ∈ j1SmallCutLowerEvent ξ Q W P K n i T L b} ≤
          ENNReal.ofReal (CN * (5 : ℝ)^K * Real.exp
            (-cN * (Real.log T')^2 / (K : ℝ)^(3 * Q.ε₀))) + g ∧
        P {ω | ∃ b ∈ I,
          ω ∈ j1SmallCutUpperEvent ξ Q W P hW K n i T L b} ≤
          ENNReal.ofReal (CP * (5 : ℝ)^K * Real.exp
            (-cP * (Real.log T')^2 /
              ((K : ℝ)^(3 * Q.ε₀) * Real.log (Real.log T')))) + g := by
  obtain ⟨p, CN, cN, CP, cP, K₀,
    hp, hpHalf, hCN, hcN, hCP, hcP, hK₀, hunit, hfull⟩ :=
    j1_small_source_full_tails_half hξ Q hε C hC
  obtain ⟨Cg, cg, hCg, hcg, hbad⟩ :=
    laneB_Xbig_real_gaussian_tail_uniform Q
  refine ⟨p, CN, cN, CP, cP, Cg, cg, K₀,
    hp, hpHalf, hCN, hcN, hCP, hcP, hCg, hcg, hK₀, hunit, ?_⟩
  intro Ω _ P W hW K n hK hKn hH i T hT
  dsimp only
  have hK64 : 64 ≤ K := hK₀.trans hK
  have hK6 : 6 ≤ K := by omega
  have hr : j1SourceRadius Q K ≤ 1 / 4 :=
    j1_source_radius_le_quarter Q K hε hK6
  have hT1 : 1 < T := by
    have hKpos : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have ha : 0 < (K : ℝ)^((1 / 2 : ℝ) + 3 * Q.ε₀) :=
      Real.rpow_pos_of_pos hKpos _
    exact (Real.one_lt_rpow (by norm_num) ha).trans hT
  have hhalf := j1_half_parameter_from_full Q K T hT
  obtain ⟨hl, hu⟩ := hfull P W hW K n hK hKn hH i
    (T^(1 / 2 : ℝ)) hhalf
  obtain ⟨htl, htu⟩ := j1_source_small_cutoff_transfer
    P W hW Q ξ hξ K n (by omega) hr i T
    (lambdaN ξ W P (n - K)) hT1
  have hg := hbad P W hW ((1 / (2 * ξ) : ℝ) * Real.log T)
    (laneB_cutoff_log_pos _ _ (j1_half_cutoff_delta ξ hξ).1 hT1)
  exact ⟨htl.trans (add_le_add hl hg),
    htu.trans (add_le_add hu hg)⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
