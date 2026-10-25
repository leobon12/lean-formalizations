import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusOsc
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBAroundCompare

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 

def laneBBlockAround (i : Bool) (v : ℂ) (K : ℕ) : Set ℂ :=
  (fun z => v + (2 : ℝ)⁻¹ ^ K • (z - (⟨1 / 2, 1 / 2⟩ : ℂ))) ''
    laneCUnitUaround i

 

theorem laneB_block_around_subset_bigBox (i : Bool) {v : ℂ} {K : ℕ}
    (hK : 3 ≤ K) (hv : v ∈ (rectAB 1 1).toSet) :
    laneBBlockAround i v K ⊆ T20D.bigBox := by
  have h₁ : laneBBlockAround i v K ⊆ laneBBlockAnnulus i v K :=
    image_mono (laneC_unit_around_subset_cross i)
  exact h₁.trans ((laneB_block_annulus_subset_closedBall i v K).trans
    (laneB_closedBall_subset_bigBox hv (laneB_small_radius_le_one hK)))

 

theorem laneB_small_annulus_cross_four_tail_implications
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (K m : ℕ) (hK : 3 ≤ K)
    (i : Bool) (v : ℂ) (hv : v ∈ (rectAB 1 1).toSet)
    (E F : Set ℂ) (t : ℝ≥0∞)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) :
    let e := ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω))
    let U := laneBBlockAnnulus i v K
    let full := crossLenIn ξ (fun x => phiMN W P 0 m x ω) U E F
    let cut := crossLenIn ξ (fun x => psiMN Q W P 0 m x ω) U E F
    (full < t → cut < e * t) ∧
    (cut < t → full < e * t) ∧
    (e * t < full → t < cut) ∧
    (e * t < cut → t < full) := by
  exact laneB_crossLen_four_tail_implications P W Q ξ ω m
    (laneBBlockAnnulus i v K) E F t
    ((laneB_block_annulus_subset_closedBall i v K).trans
      (laneB_closedBall_subset_bigBox hv (laneB_small_radius_le_one hK))) hfin

 

theorem laneB_small_annulus_around_four_tail_implications
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (Q : PsiParams) (ξ : ℝ)
    (ω : Ω) (K m : ℕ) (hK : 3 ≤ K)
    (i : Bool) (v : ℂ) (hv : v ∈ (rectAB 1 1).toSet)
    (E F : Set ℂ) (t : ℝ≥0∞)
    (hf : Continuous fun x => phiMN W P 0 m x ω)
    (hg : Continuous fun x => psiMN Q W P 0 m x ω)
    (hfin : XAB (fun n y => phiMN W P 0 n (y + T20C.cBig) ω)
      (fun n y => psiMN Q W P 0 n (y + T20C.cBig) ω) 5 5 ≠ ⊤) :
    let e := ENNReal.ofReal (Real.exp (|ξ| * T20C.Xbig Q W P ω))
    let U := laneBBlockAround i v K
    let full := (lfppContMetric ξ (fun x => phiMN W P 0 m x ω) hf).aroundDist U E F
    let cut := (lfppContMetric ξ (fun x => psiMN Q W P 0 m x ω) hg).aroundDist U E F
    (full < t → cut < e * t) ∧
    (cut < t → full < e * t) ∧
    (e * t < full → t < cut) ∧
    (e * t < cut → t < full) := by
  exact laneB_aroundDist_four_tail_implications P W Q ξ ω m
    (laneBBlockAround i v K) E F t
    (laneB_block_around_subset_bigBox i hK hv) hf hg hfin

end SupercriticalLQGUniqueness.B2.DG20Conc
