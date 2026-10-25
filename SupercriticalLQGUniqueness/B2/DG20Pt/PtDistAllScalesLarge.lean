import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistRateScaleENN

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem exists_pt_dist_all_scales_large_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (V : Set ℂ) (hV : Bornology.IsBounded V) (hconv : Convex ℝ V)
    (R : ℝ) (hR : 0 < R) :
    ∃ Cnet : ℕ, 0 < Cnet ∧
    ∃ C a₀ a₁ b₀ b₁ D σ2 H : ℝ,
      0 < C ∧ 0 < a₀ ∧ 0 < a₁ ∧ 0 < b₀ ∧ 0 < b₁ ∧
      0 < D ∧ 0 < σ2 ∧ 3 ≤ H ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ T : ℝ, Real.exp H ≤ T →
          ∃ F : ℕ → Finset ℂ,
            (∀ k ≤ n, (F k).card ≤ Cnet * 4 ^ k ∧
              ∀ z ∈ V, ∃ x ∈ F k,
                dist z x < ((2 : ℝ)⁻¹) ^ (k + 2)) ∧
            P (ptDistAllScalesGood P W ξ Q ζ C n F V R T
              (fun k => (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))))ᶜ ≤
              ENNReal.ofReal
                (2 * ((Cnet : ℝ) * a₀) *
                  Real.exp (-(a₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
                 2 * ((Cnet : ℝ) * b₀) *
                  Real.exp (-(b₁ / 2) * ((Real.log T) ^ 2 / Real.log (Real.log T))) +
                 2 * D * Real.exp (-(1 / (2 * σ2 * (R * (ξ : ℝ)) ^ 2) / 2) *
                   (Real.log T) ^ 2)) := by
  obtain ⟨Cnet, hCnet, C, a₀, a₁, b₀, b₁, D, σ2,
    hC, ha₀, ha₁, hb₀, hb₁, hD, hσ2, hevent⟩ :=
      exists_pt_dist_all_scales_event_of_inputs
        hPerc hExp ξ Q hQ ζ hζ V hV hconv R hR
  obtain ⟨H, hH, hrate⟩ :=
    pt_dist_scale_rate_sum_large Cnet a₀ a₁ b₀ b₁ D σ2 ζ R (ξ : ℝ)
      ha₀.le ha₁ hb₀.le hb₁ hD.le hσ2 hζ hR ξ.2
  refine ⟨Cnet, hCnet, C, a₀, a₁, b₀, b₁, D, σ2, H,
    hC, ha₀, ha₁, hb₀, hb₁, hD, hσ2, hH, ?_⟩
  intro Ω _ P _ W hW n T hT
  have hT0 : 0 < T := (Real.exp_pos H).trans_le hT
  have hlogT : 0 ≤ Real.log T := by
    have h := (Real.le_log_iff_exp_le hT0).2 hT
    linarith
  have ht (k : ℕ) (_hk : k ≤ n) :
      0 ≤ (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ)) := by
    apply div_nonneg
    · exact add_nonneg hlogT (mul_nonneg hζ.le (Nat.cast_nonneg k))
    · exact (mul_pos hR ξ.2).le
  have hT3 : 3 < T := by
    have hExp : Real.exp 3 > 3 := by
      nlinarith [Real.add_one_le_exp (3 : ℝ)]
    exact lt_of_lt_of_le (lt_of_lt_of_le hExp (Real.exp_le_exp.mpr hH)) hT
  obtain ⟨F, hcover, hbad⟩ :=
    hevent P W hW n T hT3
      (fun k => (Real.log T + ζ * (k : ℝ)) / (R * (ξ : ℝ))) ht
  refine ⟨F, hcover, ?_⟩
  exact hbad.trans (hrate T hT (n + 1))

end SupercriticalLQGUniqueness.B2.DG20Pt
