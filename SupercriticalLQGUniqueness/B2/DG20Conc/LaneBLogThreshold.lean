import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBBoundedCompare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 


theorem laneB_cutoff_factor_log_eq (ξ δ T : ℝ) (hT : 0 < T) :
    ENNReal.ofReal (Real.exp (|ξ| * (δ * Real.log T))) =
      ENNReal.ofReal (T ^ (δ * |ξ|)) := by
  congr 1
  rw [Real.rpow_def_of_pos hT]
  congr 1
  ring

 

theorem laneB_cutoff_log_pos (δ T : ℝ) (hδ : 0 < δ) (hT : 1 < T) :
    0 < δ * Real.log T :=
  mul_pos hδ (Real.log_pos hT)

 

theorem laneB_crossLen_four_tail_implications_log
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (m : ℕ) (U A B : Set ℂ) (t : ℝ≥0∞) (δ T : ℝ)
    (hU : U ⊆ T20D.bigBox) (hT : 1 < T)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤)
    (hgood : T20C.Xbig Q W P ω ≤ δ * Real.log T) :
    let e := ENNReal.ofReal (T ^ (δ * |ξ|))
    let full := crossLenIn ξ (fun z => phiMN W P 0 m z ω) U A B
    let cut := crossLenIn ξ (fun z => psiMN Q W P 0 m z ω) U A B
    (full < t → cut < e * t) ∧
    (cut < t → full < e * t) ∧
    (e * t < full → t < cut) ∧
    (e * t < cut → t < full) := by
  have h := laneB_crossLen_four_tail_implications_bounded P W Q ξ ω m U A B t
    (δ * Real.log T) hU hfin hgood
  simpa only [laneB_cutoff_factor_log_eq ξ δ T (by linarith)] using h

 

theorem laneB_aroundDist_four_tail_implications_log
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (m : ℕ) (U E F : Set ℂ) (t : ℝ≥0∞) (δ T : ℝ)
    (hU : U ⊆ T20D.bigBox) (hT : 1 < T)
    (hf : Continuous fun z => phiMN W P 0 m z ω)
    (hg : Continuous fun z => psiMN Q W P 0 m z ω)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤)
    (hgood : T20C.Xbig Q W P ω ≤ δ * Real.log T) :
    let e := ENNReal.ofReal (T ^ (δ * |ξ|))
    let full := (lfppContMetric ξ (fun z => phiMN W P 0 m z ω) hf).aroundDist U E F
    let cut := (lfppContMetric ξ (fun z => psiMN Q W P 0 m z ω) hg).aroundDist U E F
    (full < t → cut < e * t) ∧
    (cut < t → full < e * t) ∧
    (e * t < full → t < cut) ∧
    (e * t < cut → t < full) := by
  have h := laneB_aroundDist_four_tail_implications_bounded P W Q ξ ω m U E F t
    (δ * Real.log T) hU hf hg hfin hgood
  simpa only [laneB_cutoff_factor_log_eq ξ δ T (by linarith)] using h

end SupercriticalLQGUniqueness.B2.DG20Conc
