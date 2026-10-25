import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBCoarseOscTail

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 

theorem laneB_coarse_square_cost_of_good_oscillation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (Q : PsiParams) (ξ : ℝ) {K : ℕ} (hK : 6 ≤ K)
    (hε : Q.ε₀ ≤ 1) (ω : Ω) {γ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ)
    (x : ℝ)
    (hgood : ¬ ∃ b ∈ j1SourceIdx K (j1SourceRadius Q K),
      ∃ z ∈ T20D.hatBox K b,
        3 * x < |phiMN W P 0 K z ω -
          phiMN W P 0 K (T20.dyCenter K b) ω|)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) :
    rectLen ξ (fun z => psiMN Q W P 0 K z ω) (rectAB 1 1) ≤
      ENNReal.ofReal
        (4 * (2 : ℝ)⁻¹ ^ K *
          ∑ b ∈ T20.coarseBlocks K γ,
            Real.exp (|ξ| * (3 * x + T20C.Xbig Q W P ω)) *
              Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) := by
  apply laneB_coarse_square_cost_of_phi_oscillation P W Q ξ hK hε ω hγ (3 * x)
  · intro b hb z hz
    exact le_of_not_gt fun hbad => hgood ⟨b, hb, z, hz, hbad⟩
  · exact hfin

end SupercriticalLQGUniqueness.B2.DG20Conc
