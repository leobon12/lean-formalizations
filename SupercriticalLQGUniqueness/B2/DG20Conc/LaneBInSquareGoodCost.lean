import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBGlueBoxOscTail

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneB_chosen_square_cost_of_good_glueBox (ξ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 3 ≤ K →
      ∃ circ : ℤ × ℤ → Finset (Circle × ℂ),
        (∀ b, ((circ b).card : ℝ) ≤ C) ∧
        ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
          (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
          (Q : PsiParams) (n : ℕ) (hKn : K ≤ n),
          ∀ᵐ ω ∂P, ∀ (γ : ℝ → ℂ),
            AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
              (rectAB 1 1).side₂ γ →
            ∀ x : ℝ,
              (¬ ∃ b ∈ T20.blkIdx K, ∃ z ∈ S6U.glueBox K b,
                7 * x < |phiMN W P 0 K z ω -
                  phiMN W P 0 K (T20.dyCenter K b) ω|) →
              lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω ≤
                Real.exp (|ξ| * (2 * T20C.Xbig Q W P ω)) *
                  (C * ∑ b ∈ T20.coarseBlocks K γ,
                    (Real.exp (|ξ| * (7 * x + T20C.Xbig Q W P ω)) *
                      Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) *
                      ∑ j ∈ circ b,
                        T20B.mrectLen ξ (fun y => phiMN W P K n y ω)
                          K j.1 j.2 3 1) := by
  classical
  obtain ⟨C, hC, hcost⟩ := laneB_chosen_square_weighted_circuit_cost ξ
  refine ⟨C, hC, ?_⟩
  intro K hK
  obtain ⟨circ, hcard, hcostK⟩ := hcost K (by omega)
  refine ⟨circ, hcard, ?_⟩
  intro Ω _ P W hW Q n hKn
  filter_upwards [hcostK P W hW Q n hKn] with ω hcostω
  intro γ hγ x hgood
  apply hcostω γ hγ (7 * x)
  intro b hb z hz
  apply le_of_not_gt
  intro hbad
  exact hgood ⟨b, (Finset.mem_filter.1 hb).1, z, hz, hbad⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
