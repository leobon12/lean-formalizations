import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBCoarseSquareCost
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBHatBoxGeometry

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 

theorem laneB_coarse_square_cost_of_phi_oscillation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (Q : PsiParams) (ξ : ℝ) {K : ℕ} (hK : 6 ≤ K)
    (hε : Q.ε₀ ≤ 1) (ω : Ω) {γ : ℝ → ℂ}
    (hγ : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ γ)
    (M : ℝ)
    (hphi : ∀ b ∈ j1SourceIdx K (j1SourceRadius Q K),
      ∀ x ∈ T20D.hatBox K b,
      |phiMN W P 0 K x ω - phiMN W P 0 K (T20.dyCenter K b) ω| ≤ M)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) :
    rectLen ξ (fun z => psiMN Q W P 0 K z ω) (rectAB 1 1) ≤
      ENNReal.ofReal
        (4 * (2 : ℝ)⁻¹ ^ K *
          ∑ b ∈ T20.coarseBlocks K γ,
            Real.exp (|ξ| * (M + T20C.Xbig Q W P ω)) *
              Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω)) := by
  have hmap : MapsTo γ (Icc (0 : ℝ) 1) L23.sq01 := by
    rcases hγ with ⟨_, _, _, _, _, hm⟩
    exact hm
  have hbmem := laneB_coarseBlocks_subset_sourceIdx Q hε hK hmap
  apply laneB_coarse_square_cost P W Q ξ K ω hγ
  intro b hb x hx
  have hbI := hbmem hb
  have hxBig := laneB_source_hatBox_subset_bigBox Q hK hbI hx
  have hcut := T20D.abs_sub_le_Xbig (P := P) (W := W) Q hfin K hxBig
  have hphi' := hphi b hbI x hx
  calc
    |psiMN Q W P 0 K x ω - phiMN W P 0 K (T20.dyCenter K b) ω| ≤
        |psiMN Q W P 0 K x ω - phiMN W P 0 K x ω| +
          |phiMN W P 0 K x ω - phiMN W P 0 K (T20.dyCenter K b) ω| :=
      abs_sub_le _ _ _
    _ ≤ M + T20C.Xbig Q W P ω := by rw [abs_sub_comm]; linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
