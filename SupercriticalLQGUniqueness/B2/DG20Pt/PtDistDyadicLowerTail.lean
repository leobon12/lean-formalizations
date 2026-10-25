import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGaussianDecay

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_univ_le_internal
    (ξ : ℝ) (φ : ℂ → ℝ) (U : Set ℂ) (z w : ℂ) :
    lfppDOn ξ φ univ z w ≤ lfppDOn ξ φ U z w := by
  refine le_iInf fun P => ?_
  exact iInf_le_of_le
    ⟨P.1, P.2.1, fun _ _ => mem_univ _⟩ le_rfl

theorem pt_dist_dyadic_lower_tail_small_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (U : Set ℂ) (z w : ℂ) (hzw : z ≠ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 3 < T ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ,
          P {ω | lfppDOn (ξ : ℝ)
            (fun y => phiMN W P 0 n y ω) U z w <
              ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ≤
            ENNReal.ofReal ε := by
  obtain ⟨c₀, c₁, hc₀, hc₁, htail⟩ :=
    pt_dist_point_lower_tail_of_inputs hPerc ξ z w hzw
  obtain ⟨T, hT, hsmall⟩ := pt_dist_gaussian_log_tail_small c₀ c₁ ε hc₀ hc₁ hε
  refine ⟨T, hT, ?_⟩
  intro Ω _ P _ W hW n
  have hsub :
      {ω | lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w <
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} ⊆
      {ω | lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) univ z w <
        ENNReal.ofReal (T⁻¹ * lambdaN ξ W P n)} := by
    intro ω hω
    exact (pt_dist_univ_le_internal (ξ : ℝ)
      (fun y => phiMN W P 0 n y ω) U z w).trans_lt hω
  exact (measure_mono hsub).trans
    ((htail P W hW n T hT).trans (ENNReal.ofReal_le_ofReal hsmall))

end SupercriticalLQGUniqueness.B2.DG20Pt
