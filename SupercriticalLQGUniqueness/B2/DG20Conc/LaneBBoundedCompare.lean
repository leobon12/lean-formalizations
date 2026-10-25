import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBAroundCompare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 

theorem laneB_cutoff_factor_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (Q : PsiParams)
    (ξ x : ℝ) (ω : Ω) (hgood : T20C.Xbig Q W P ω ≤ x) :
    ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω)) ≤
      ENNReal.ofReal (Real.exp (|ξ| * x)) := by
  apply ENNReal.ofReal_le_ofReal
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hgood (abs_nonneg ξ))

 

theorem laneB_crossLen_four_tail_implications_bounded
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (m : ℕ) (U A B : Set ℂ) (t : ℝ≥0∞) (x : ℝ)
    (hU : U ⊆ T20D.bigBox)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤)
    (hgood : T20C.Xbig Q W P ω ≤ x) :
    let e := ENNReal.ofReal (Real.exp (|ξ| * x))
    let full := crossLenIn ξ (fun z => phiMN W P 0 m z ω) U A B
    let cut := crossLenIn ξ (fun z => psiMN Q W P 0 m z ω) U A B
    (full < t → cut < e * t) ∧
    (cut < t → full < e * t) ∧
    (e * t < full → t < cut) ∧
    (e * t < cut → t < full) := by
  dsimp
  have hcmp := laneB_crossLen_compare_cutoff P W Q ξ ω m U A B hU hfin
  have he := laneB_cutoff_factor_le P W Q ξ x ω hgood
  apply laneB_four_tail_implications
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
  · exact hcmp.1.trans (mul_le_mul_of_nonneg_right he bot_le)
  · exact hcmp.2.trans (mul_le_mul_of_nonneg_right he bot_le)

 

theorem laneB_aroundDist_four_tail_implications_bounded
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (m : ℕ) (U E F : Set ℂ) (t : ℝ≥0∞) (x : ℝ)
    (hU : U ⊆ T20D.bigBox)
    (hf : Continuous fun z => phiMN W P 0 m z ω)
    (hg : Continuous fun z => psiMN Q W P 0 m z ω)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤)
    (hgood : T20C.Xbig Q W P ω ≤ x) :
    let e := ENNReal.ofReal (Real.exp (|ξ| * x))
    let full := (lfppContMetric ξ (fun z => phiMN W P 0 m z ω) hf).aroundDist U E F
    let cut := (lfppContMetric ξ (fun z => psiMN Q W P 0 m z ω) hg).aroundDist U E F
    (full < t → cut < e * t) ∧
    (cut < t → full < e * t) ∧
    (e * t < full → t < cut) ∧
    (e * t < cut → t < full) := by
  dsimp
  have hcmp := laneB_aroundDist_compare_cutoff P W Q ξ ω m U E F hU hf hg hfin
  have he := laneB_cutoff_factor_le P W Q ξ x ω hgood
  apply laneB_four_tail_implications
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top
  · exact hcmp.1.trans (mul_le_mul_of_nonneg_right he bot_le)
  · exact hcmp.2.trans (mul_le_mul_of_nonneg_right he bot_le)

end SupercriticalLQGUniqueness.B2.DG20Conc
