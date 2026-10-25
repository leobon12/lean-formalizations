import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInSquareFieldSplit

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneB_in_square_chosen_cutoff_glue (ξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 2 ≤ K →
      ∃ circ : ℤ × ℤ → Finset (Circle × ℂ),
        (∀ b, ((circ b).card : ℝ) ≤ C) ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
          (Q : PsiParams) (n : ℕ) (hKn : K ≤ n),
          ∀ᵐ ω ∂P, ∀ (γ : ℝ → ℂ),
            AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
              (rectAB 1 1).side₂ γ →
            ∀ w : ℤ × ℤ → ℝ,
              (∀ b ∈ T20.coarseBlocks K γ, ∀ x ∈ S6U.glueBox K b,
                Real.exp (ξ * psiMN Q W P 0 K x ω) ≤ w b) →
              lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω ≤
                Real.exp (|ξ| * (2 * T20C.Xbig Q W P ω)) *
                  (C * ∑ b ∈ T20.coarseBlocks K γ,
                    w b * ∑ j ∈ circ b,
                      T20B.mrectLen ξ (fun x => phiMN W P K n x ω)
                        K j.1 j.2 3 1) := by
  obtain ⟨C, hC, hglue⟩ := laneB_in_square_glue_chosen_coarse ξ
  refine ⟨C, hC, ?_⟩
  intro K hK
  obtain ⟨circ, hcard, hcost⟩ := hglue K hK
  refine ⟨circ, hcard, ?_⟩
  intro Ω _ P W hW Q n hKn
  filter_upwards [laneB_ae_chosen_cutoff_square_split P W hW Q hKn]
    with ω hsplit
  intro γ hγ w hw
  have hcont : Continuous (fun x => psiMN Q W P 0 K x ω +
      phiMN W P K n x ω) :=
    ((isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)).cont ω).add
      ((isPhiVersion_phiMN hW hKn).cont ω)
  have hcmp := laneB_in_square_cutoff_le_of_split
    (ξ := ξ) (M := 2 * T20C.Xbig Q W P ω) hcont hsplit
  change lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω ≤ _ at hcmp
  exact hcmp.trans (mul_le_mul_of_nonneg_left
    (hcost P W hW Q n hKn ω γ hγ w hw) (Real.exp_pos _).le)

end SupercriticalLQGUniqueness.B2.DG20Conc
