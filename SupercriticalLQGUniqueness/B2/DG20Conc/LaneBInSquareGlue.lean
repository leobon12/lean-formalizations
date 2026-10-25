import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBCoarseGoodCost
import LQGMetric.Papers.DDDF.S6P26Glue3

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 


theorem laneB_in_square_glue_chosen_coarse (ξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 2 ≤ K →
      ∃ circ : ℤ × ℤ → Finset (Circle × ℂ),
        (∀ b, ((circ b).card : ℝ) ≤ C) ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
          (Q : PsiParams) (n : ℕ) (hKn : K ≤ n) (ω : Ω)
          (γ : ℝ → ℂ),
          AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
            (rectAB 1 1).side₂ γ →
          ∀ w : ℤ × ℤ → ℝ,
            (∀ b ∈ T20.coarseBlocks K γ, ∀ x ∈ S6U.glueBox K b,
              Real.exp (ξ * psiMN Q W P 0 K x ω) ≤ w b) →
            (rectLen ξ (fun x => psiMN Q W P 0 K x ω +
              phiMN W P K n x ω) (rectAB 1 1)).toReal ≤
              C * ∑ b ∈ T20.coarseBlocks K γ,
                w b * ∑ j ∈ circ b,
                  T20B.mrectLen ξ (fun x => phiMN W P K n x ω)
                    K j.1 j.2 3 1 := by
  obtain ⟨C, hC, hglue⟩ := s6_step1_glue ξ
  refine ⟨C, hC, ?_⟩
  intro K hK
  obtain ⟨circ, hcard, hcost⟩ := hglue K hK
  refine ⟨circ, hcard, ?_⟩
  intro Ω _ P W hW Q n hKn ω γ hγ w hw
  exact hcost (fun x => psiMN Q W P 0 K x ω)
    (fun x => phiMN W P K n x ω)
    ((isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)).cont ω)
    ((isPhiVersion_phiMN hW hKn).cont ω)
    γ hγ w hw

end SupercriticalLQGUniqueness.B2.DG20Conc
