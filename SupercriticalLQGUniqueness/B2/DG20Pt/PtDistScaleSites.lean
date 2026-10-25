import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSiteEvent
import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNet

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptDistAllSitesGood {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ)
    (F : Finset ℂ) (T : ℝ) : Set Ω :=
  {ω | ∀ x ∈ F, ω ∈ ptDistSiteGood P W ξ Q ζ C n k x T}

 

theorem pt_dist_all_sites_bad_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k : ℕ)
    (F : Finset ℂ) (T : ℝ) (R : ℝ≥0∞)
    (hsite : ∀ x ∈ F,
      P (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ ≤ R) :
    P (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ ≤ (F.card : ℝ≥0∞) * R := by
  have hsub : (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ ⊆
      ⋃ x ∈ F, (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ := by
    intro ω hω
    simp only [ptDistAllSitesGood, mem_compl_iff, mem_ofPred_eq,
      not_forall, mem_iUnion, mem_compl_iff] at hω ⊢
    obtain ⟨x, hx⟩ := hω
    exact ⟨x, hx.1, hx.2⟩
  calc
    P (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ ≤
        P (⋃ x ∈ F, (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ) := measure_mono hsub
    _ ≤ ∑ x ∈ F, P (ptDistSiteGood P W ξ Q ζ C n k x T)ᶜ :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ _x ∈ F, R := Finset.sum_le_sum fun x hx => hsite x hx
    _ = (F.card : ℝ≥0∞) * R := by simp

 

theorem exists_pt_dist_scale_sites_of_inputs
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
          ∃ F : Finset ℂ,
            F.card ≤ Cnet * 4 ^ k ∧
            (∀ z ∈ V, ∃ x ∈ F, dist z x < ((2 : ℝ)⁻¹) ^ (k + 2)) ∧
            P (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ ≤
              ((Cnet * 4 ^ k : ℕ) : ℝ≥0∞) *
                (ENNReal.ofReal (a₀ * Real.exp
                  (-a₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
                 ENNReal.ofReal (b₀ * Real.exp
                  (-b₁ * (Real.log T) ^ 2 / Real.log (Real.log T)))) := by
  obtain ⟨Cnet, hCnet, hnet⟩ := exists_pt_dist_net V hV
  obtain ⟨C, a₀, a₁, b₀, b₁, hC, ha₀, ha₁, hb₀, hb₁, htail⟩ :=
    pt_dist_site_bad_tail_of_inputs hPerc hExp ξ Q hQ ζ hζ
  refine ⟨Cnet, hCnet, C, a₀, a₁, b₀, b₁,
    hC, ha₀, ha₁, hb₀, hb₁, ?_⟩
  intro Ω _ P _ W hW n k hkn T hT
  obtain ⟨F, hcard, hcover⟩ := hnet k
  refine ⟨F, hcard, hcover, ?_⟩
  have hbound := pt_dist_all_sites_bad_le P W ξ Q ζ C n k F T
    (ENNReal.ofReal (a₀ * Real.exp
      (-a₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
     ENNReal.ofReal (b₀ * Real.exp
      (-b₁ * (Real.log T) ^ 2 / Real.log (Real.log T))))
    (fun x _ => htail P W hW n k hkn x T hT)
  exact hbound.trans (by gcongr)

end SupercriticalLQGUniqueness.B2.DG20Pt
