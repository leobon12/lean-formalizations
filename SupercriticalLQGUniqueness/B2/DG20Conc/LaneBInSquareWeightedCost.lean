import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInSquareCoarseWeight

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneB_chosen_square_weighted_circuit_cost (ξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 2 ≤ K →
      ∃ circ : ℤ × ℤ → Finset (Circle × ℂ),
        (∀ b, ((circ b).card : ℝ) ≤ C) ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
          (Q : PsiParams) (n : ℕ) (hKn : K ≤ n),
          ∀ᵐ ω ∂P, ∀ (γ : ℝ → ℂ),
            AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
              (rectAB 1 1).side₂ γ →
            ∀ M : ℝ,
              (∀ b ∈ T20.coarseBlocks K γ,
                ∀ x ∈ S6U.glueBox K b,
                  |phiMN W P 0 K x ω -
                    phiMN W P 0 K (T20.dyCenter K b) ω| ≤ M) →
              lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω ≤
                Real.exp (|ξ| * (2 * T20C.Xbig Q W P ω)) *
                  (C * ∑ b ∈ T20.coarseBlocks K γ,
                    (Real.exp (|ξ| * (M + T20C.Xbig Q W P ω)) *
                      Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
                      ∑ j ∈ circ b,
                        T20B.mrectLen ξ (fun x => phiMN W P K n x ω)
                          K j.1 j.2 3 1) := by
  obtain ⟨C, hC, hglue⟩ := laneB_in_square_chosen_cutoff_glue ξ
  refine ⟨C, hC, ?_⟩
  intro K hK
  obtain ⟨circ, hcard, hcost⟩ := hglue K hK
  refine ⟨circ, hcard, ?_⟩
  intro Ω _ P W hW Q n hKn
  filter_upwards [hcost P W hW Q n hKn,
    T20D.ae_XAB_shift_ne_top hW Q T20C.cBig 5 5]
    with ω hcostω hfin
  intro γ hγ M hosc
  exact hcostω γ hγ _
    (laneB_chosen_coarse_glueBox_weight P W Q ξ hK ω M hosc hfin)

end SupercriticalLQGUniqueness.B2.DG20Conc
