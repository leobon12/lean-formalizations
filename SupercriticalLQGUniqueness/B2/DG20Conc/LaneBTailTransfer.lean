import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBFieldCompare

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 

theorem laneB_four_tail_implications
    {x y e t : ℝ≥0∞} (he0 : e ≠ 0) (heTop : e ≠ ⊤)
    (hxy : x ≤ e * y) (hyx : y ≤ e * x) :
    (x < t → y < e * t) ∧
    (y < t → x < e * t) ∧
    (e * t < x → t < y) ∧
    (e * t < y → t < x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h' : e * x < e * t := by
      simpa only [mul_comm] using ENNReal.mul_lt_mul_left he0 heTop h
    exact lt_of_le_of_lt hyx h'
  · intro h
    have h' : e * y < e * t := by
      simpa only [mul_comm] using ENNReal.mul_lt_mul_left he0 heTop h
    exact lt_of_le_of_lt hxy h'
  · intro h
    have h' : t * e < y * e := by
      simpa only [mul_comm] using (lt_of_lt_of_le h hxy)
    exact (ENNReal.mul_lt_mul_iff_left he0 heTop).mp h'
  · intro h
    have h' : t * e < x * e := by
      simpa only [mul_comm] using (lt_of_lt_of_le h hyx)
    exact (ENNReal.mul_lt_mul_iff_left he0 heTop).mp h'

 

theorem laneB_crossLen_four_tail_implications
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (m : ℕ) (U A B : Set ℂ) (t : ℝ≥0∞)
    (hU : U ⊆ T20D.bigBox)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) :
    let e := ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω))
    let full := crossLenIn ξ (fun x => phiMN W P 0 m x ω) U A B
    let cut := crossLenIn ξ (fun x => psiMN Q W P 0 m x ω) U A B
    (full < t → cut < e * t) ∧
    (cut < t → full < e * t) ∧
    (e * t < full → t < cut) ∧
    (e * t < cut → t < full) := by
  dsimp
  have hcmp := laneB_crossLen_compare_cutoff P W Q ξ ω m U A B hU hfin
  exact laneB_four_tail_implications
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    ENNReal.ofReal_ne_top hcmp.1 hcmp.2

end SupercriticalLQGUniqueness.B2.DG20Conc
