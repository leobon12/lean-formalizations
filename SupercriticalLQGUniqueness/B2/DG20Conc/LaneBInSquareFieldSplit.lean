import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBInSquareCutoffCompare
import LQGMetric.Papers.DDDF.P18Step2

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneB_unit_square_subset_bigBox :
    (rectAB 1 1).toSet ⊆ T20D.bigBox := by
  intro x hx
  simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc,
    zero_add] at hx
  simp only [T20D.bigBox, Complex.mem_reProdIm, mem_Icc]
  rcases hx with ⟨⟨hxr0, hxr1⟩, ⟨hxi0, hxi1⟩⟩
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

 

theorem laneB_ae_chosen_cutoff_square_split
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n) :
    ∀ᵐ ω ∂P, ∀ x ∈ (rectAB 1 1).toSet,
      |psiMN Q W P 0 n x ω -
        (psiMN Q W P 0 K x ω + phiMN W P K n x ω)| ≤
        2 * T20C.Xbig Q W P ω := by
  filter_upwards [T20D.ae_XAB_shift_ne_top hW Q T20C.cBig 5 5,
    ae_phiMN_add hW hKn] with ω hfin hadd
  intro x hx
  have hxB := laneB_unit_square_subset_bigBox hx
  have hn := T20D.abs_sub_le_Xbig (P := P) (W := W) Q hfin n hxB
  have hK := T20D.abs_sub_le_Xbig (P := P) (W := W) Q hfin K hxB
  have hn' := (abs_le.mp hn)
  have hK' := (abs_le.mp hK)
  apply abs_le.mpr
  constructor <;> nlinarith [hn'.1, hn'.2, hK'.1, hK'.2, hadd x]

end SupercriticalLQGUniqueness.B2.DG20Conc
