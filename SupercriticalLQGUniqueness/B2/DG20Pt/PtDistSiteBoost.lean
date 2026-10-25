import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleSites

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_boost_coeff (ξ Q ζ T : ℝ) (k : ℕ) :
    (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))) *
      (2 : ℝ) ^ (-(ξ * Q - ζ / 2) * (k : ℝ)) =
    T * (2 : ℝ) ^ (-(ξ * Q - ζ) * (k : ℝ)) := by
  rw [mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring_nf

theorem pt_dist_boost_gt_three (ζ : ℝ) (hζ : 0 < ζ)
    (k : ℕ) (T : ℝ) (hT : 3 < T) :
    3 < T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)) := by
  have hpow : 1 ≤ (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  nlinarith

theorem pt_dist_site_good_boost {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ) (x : ℂ) (T : ℝ) :
    ptDistSiteGood P W ξ Q ζ C n k x T =
      ptDistSiteGood P W ξ Q (ζ / 2) C n k x
        (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))) := by
  have hcoef := pt_dist_boost_coeff (ξ : ℝ) Q ζ T k
  have hA :
      (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))) *
        ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ / 2) * (k : ℝ)) *
          lambdaN ξ W P n) =
      T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
        lambdaN ξ W P n) := by
    calc
      _ = ((T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))) *
          (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ / 2) * (k : ℝ))) *
          lambdaN ξ W P n := by ring
      _ = _ := by rw [hcoef]; ring
  have hB :
      (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))) *
        (C * (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ / 2) * (k : ℝ)) *
          lambdaN ξ W P n) =
      T * (C * (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) *
        lambdaN ξ W P n) := by
    calc
      _ = C * ((T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))) *
          (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ / 2) * (k : ℝ))) *
          lambdaN ξ W P n := by ring
      _ = _ := by rw [hcoef]; ring
  unfold ptDistSiteGood
  ext ω
  simp only [mem_ofPred_eq]
  rw [hA]
  have hBω := congrArg (fun a : ℝ => a * Real.exp ((ξ : ℝ) * phiMN W P 0 k x ω)) hB
  rw [hBω]

 

theorem pt_dist_site_bad_boost_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ C a₀ a₁ b₀ b₁ : ℝ,
      0 < C ∧ 0 < a₀ ∧ 0 < a₁ ∧ 0 < b₀ ∧ 0 < b₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ x : ℂ,
          ∀ T : ℝ, 3 < T →
          let S : ℝ := T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))
          P (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ ≤
            ENNReal.ofReal (a₀ * Real.exp
              (-a₁ * (Real.log S) ^ 2 / Real.log (Real.log S))) +
            ENNReal.ofReal (b₀ * Real.exp
              (-b₁ * (Real.log S) ^ 2 / Real.log (Real.log S))) := by
  obtain ⟨C, a₀, a₁, b₀, b₁, hC, ha₀, ha₁, hb₀, hb₁, htail⟩ :=
    pt_dist_site_bad_tail_of_inputs hPerc hExp ξ Q hQ (ζ / 2) (by positivity)
  refine ⟨C, a₀, a₁, b₀, b₁, hC, ha₀, ha₁, hb₀, hb₁, ?_⟩
  intro Ω _ P _ W hW n k hkn x T hT
  rw [pt_dist_site_good_boost]
  exact htail P W hW n k hkn x _ (pt_dist_boost_gt_three ζ hζ k T hT)

 
theorem exists_pt_dist_scale_sites_boost_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (V : Set ℂ) (hV : Bornology.IsBounded V) :
    ∃ Cnet : ℕ, 0 < Cnet ∧
    ∃ C a₀ a₁ b₀ b₁ : ℝ,
      0 < C ∧ 0 < a₀ ∧ 0 < a₁ ∧ 0 < b₀ ∧ 0 < b₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n → ∀ T : ℝ, 3 < T →
          let S : ℝ := T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))
          ∃ F : Finset ℂ,
            F.card ≤ Cnet * 4 ^ k ∧
            (∀ z ∈ V, ∃ x ∈ F, dist z x < ((2 : ℝ)⁻¹) ^ (k + 2)) ∧
            P (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ ≤
              ((Cnet * 4 ^ k : ℕ) : ℝ≥0∞) *
                (ENNReal.ofReal (a₀ * Real.exp
                  (-a₁ * (Real.log S) ^ 2 / Real.log (Real.log S))) +
                 ENNReal.ofReal (b₀ * Real.exp
                  (-b₁ * (Real.log S) ^ 2 / Real.log (Real.log S)))) := by
  obtain ⟨Cnet, hCnet, hnet⟩ := exists_pt_dist_net V hV
  obtain ⟨C, a₀, a₁, b₀, b₁, hC, ha₀, ha₁, hb₀, hb₁, htail⟩ :=
    pt_dist_site_bad_boost_of_inputs hPerc hExp ξ Q hQ ζ hζ
  refine ⟨Cnet, hCnet, C, a₀, a₁, b₀, b₁,
    hC, ha₀, ha₁, hb₀, hb₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  obtain ⟨F, hcard, hcover⟩ := hnet k
  refine ⟨F, hcard, hcover, ?_⟩
  have hbound := pt_dist_all_sites_bad_le P W ξ Q ζ C n k F T
    (ENNReal.ofReal (a₀ * Real.exp
      (-a₁ * (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))) ^ 2 /
        Real.log (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))))) +
     ENNReal.ofReal (b₀ * Real.exp
      (-b₁ * (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))) ^ 2 /
        Real.log (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))))))
    (fun x _ => htail P W hW n k hkn x T hT)
  exact hbound.trans (by gcongr)

end SupercriticalLQGUniqueness.B2.DG20Pt
