import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBLogThreshold

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

 


theorem laneB_measure_le_of_ae_good_imp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B Bad : Set Ω)
    (h : ∀ᵐ ω ∂P, ω ∈ A → ω ∉ Bad → ω ∈ B) :
    P A ≤ P B + P Bad := by
  calc
    P A ≤ P (B ∪ Bad) := by
      apply measure_mono_ae
      filter_upwards [h] with ω hω hA
      by_cases hbad : ω ∈ Bad
      · exact Or.inr hbad
      · exact Or.inl (hω hA hbad)
    _ ≤ P B + P Bad := measure_union_le _ _

 



theorem laneB_crossLen_four_probability_comparisons_log
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) (ξ : ℝ) (m : ℕ) (U A B : Set ℂ)
    (t : ℝ≥0∞) (δ T : ℝ) (hU : U ⊆ T20D.bigBox) (hT : 1 < T) :
    let e := ENNReal.ofReal (T ^ (δ * |ξ|))
    let full := fun ω => crossLenIn ξ (fun z => phiMN W P 0 m z ω) U A B
    let cut := fun ω => crossLenIn ξ (fun z => psiMN Q W P 0 m z ω) U A B
    let bad := {ω | δ * Real.log T ≤ T20C.Xbig Q W P ω}
    P {ω | full ω < t} ≤ P {ω | cut ω < e * t} + P bad ∧
    P {ω | cut ω < t} ≤ P {ω | full ω < e * t} + P bad ∧
    P {ω | e * t < full ω} ≤ P {ω | t < cut ω} + P bad ∧
    P {ω | e * t < cut ω} ≤ P {ω | t < full ω} + P bad := by
  dsimp
  have hfin := T20D.ae_XAB_shift_ne_top hW Q T20C.cBig 5 5
  have hcmp : ∀ᵐ ω ∂P,
      ω ∉ {ω | δ * Real.log T ≤ T20C.Xbig Q W P ω} →
      let e := ENNReal.ofReal (T ^ (δ * |ξ|))
      let full := crossLenIn ξ (fun z => phiMN W P 0 m z ω) U A B
      let cut := crossLenIn ξ (fun z => psiMN Q W P 0 m z ω) U A B
      (full < t → cut < e * t) ∧
      (cut < t → full < e * t) ∧
      (e * t < full → t < cut) ∧
      (e * t < cut → t < full) := by
    filter_upwards [hfin] with ω hω hgood
    exact laneB_crossLen_four_tail_implications_log P W Q ξ ω m U A B t δ T
      hU hT hω (le_of_lt (lt_of_not_ge hgood))
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply laneB_measure_le_of_ae_good_imp P
    filter_upwards [hcmp] with ω hω hA hgood
    exact (hω hgood).1 hA
  · apply laneB_measure_le_of_ae_good_imp P
    filter_upwards [hcmp] with ω hω hA hgood
    exact (hω hgood).2.1 hA
  · apply laneB_measure_le_of_ae_good_imp P
    filter_upwards [hcmp] with ω hω hA hgood
    exact (hω hgood).2.2.1 hA
  · apply laneB_measure_le_of_ae_good_imp P
    filter_upwards [hcmp] with ω hω hA hgood
    exact (hω hgood).2.2.2 hA

 


theorem laneB_aroundDist_four_probability_comparisons_log
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Q : PsiParams) (ξ : ℝ) (m : ℕ) (U E F : Set ℂ)
    (t : ℝ≥0∞) (δ T : ℝ) (hU : U ⊆ T20D.bigBox) (hT : 1 < T) :
    let e := ENNReal.ofReal (T ^ (δ * |ξ|))
    let full := fun ω =>
      (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist U E F
    let cut := fun ω =>
      (lfppContMetric ξ (fun z => psiMN Q W P 0 m z ω)
        ((isPsiVersion_psiMN hW (Nat.zero_le m)).cont ω)).aroundDist U E F
    let bad := {ω | δ * Real.log T ≤ T20C.Xbig Q W P ω}
    P {ω | full ω < t} ≤ P {ω | cut ω < e * t} + P bad ∧
    P {ω | cut ω < t} ≤ P {ω | full ω < e * t} + P bad ∧
    P {ω | e * t < full ω} ≤ P {ω | t < cut ω} + P bad ∧
    P {ω | e * t < cut ω} ≤ P {ω | t < full ω} + P bad := by
  dsimp
  have hfin := T20D.ae_XAB_shift_ne_top hW Q T20C.cBig 5 5
  have hcmp : ∀ᵐ ω ∂P,
      ω ∉ {ω | δ * Real.log T ≤ T20C.Xbig Q W P ω} →
      let e := ENNReal.ofReal (T ^ (δ * |ξ|))
      let full := (lfppContMetric ξ (fun z => phiMN W P 0 m z ω)
        ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)).aroundDist U E F
      let cut := (lfppContMetric ξ (fun z => psiMN Q W P 0 m z ω)
        ((isPsiVersion_psiMN hW (Nat.zero_le m)).cont ω)).aroundDist U E F
      (full < t → cut < e * t) ∧
      (cut < t → full < e * t) ∧
      (e * t < full → t < cut) ∧
      (e * t < cut → t < full) := by
    filter_upwards [hfin] with ω hω hgood
    exact laneB_aroundDist_four_tail_implications_log P W Q ξ ω m U E F t δ T
      hU hT ((isPhiVersion_phiMN hW (Nat.zero_le m)).cont ω)
      ((isPsiVersion_psiMN hW (Nat.zero_le m)).cont ω)
      hω (le_of_lt (lt_of_not_ge hgood))
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply laneB_measure_le_of_ae_good_imp P
    filter_upwards [hcmp] with ω hω hA hgood
    exact (hω hgood).1 hA
  · apply laneB_measure_le_of_ae_good_imp P
    filter_upwards [hcmp] with ω hω hA hgood
    exact (hω hgood).2.1 hA
  · apply laneB_measure_le_of_ae_good_imp P
    filter_upwards [hcmp] with ω hω hA hgood
    exact (hω hgood).2.2.1 hA
  · apply laneB_measure_le_of_ae_good_imp P
    filter_upwards [hcmp] with ω hω hA hgood
    exact (hω hgood).2.2.2 hA

end SupercriticalLQGUniqueness.B2.DG20Conc
