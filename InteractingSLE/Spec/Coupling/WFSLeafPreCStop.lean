/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPreCClause
import InteractingSLE.Spec.Coupling.WFS2GermBridge

/-!
# Regular stopped couplings strictly before a through cutoff

A stopping time strictly before the through cutoff gives a closed stopped
coupling with the original field and coordinates. The only change is the usual
augmentation of the evolution filtration. The closed-record reader supplies the
conditional-law clause at the endpoint; the original full path supplies regularity.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique LQGMetric Restart.StoppedExtendWF Restart.StoppedExtend Restart.Aux54

/-- A strictly earlier driving stop supplies the complete regular stopped
coupling required by Aux. 54, keeping the original field on the original space. -/
theorem isStoppedHullCoupling_of_through_strict
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    {S : Ω → ℝ≥0∞}
    (hS : IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose)
      fun ω => (S ω : WithTop ℝ≥0))
    (hle : ∀ ω, S ω ≤ V ω) (hSV : ∀ᵐ ω ∂P, S ω < V ω) :
    IsStoppedHullCoupling κ xL xR ρL ρR P (usualAugmentation 𝓕 P) W VL VR B S h ∧
      IsRegularStop ρL ρR P W VL VR S := by
  have hXV := hC.2.2.2.2.choose
  have hcl := hC.2.2.2.2.choose_spec
  have hXF := Coupling.IsIntegratedSLEEvolution.isMeasurableKilledDriving hC.1
  have hSm : Measurable S := hS.measurable.mono hS.measurableSpace_le le_rfl
  have hXS := isMeasurableKilledDriving_of_le hXV hSm hle
  have hfil := drivingFiltration_le_of_earlier_stop hXV hXS hS hle
  have hSfull := isStoppingTime_full_drivingFiltration_of_lt hXF hXV hC.2.1 hS hSV
  have hSF := Ito.isStoppingTime_usualAugmentation_of_drivingFiltration hC.1 hXF hSfull
  have hEv := (Ito.isIntegratedSLEEvolution_usualAugmentation hC.1).isSLEEvolutionUpTo.mono
    hSF (fun ω => (hle ω).trans (hC.2.1 ω))
  have hc : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = S ω →
      ContinuousOn (dState W VL VR ω) (Iic T) := by
    filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path, hSV] with ω hp hs T hT
    have ht : (T : ℝ≥0∞) < ζ ω := hT.trans_lt (hs.trans_le (hC.2.1 ω))
    exact (continuousOn_state_of_isSLEPathUpTo hp).mono fun t htT =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 htT) ht
  refine ⟨⟨hEv, hc, hC.2.2.1, hC.2.2.2.1, hXS, ?_⟩, ?_⟩
  · intro τ hτ hτS
    have hτV : IsStoppingTime (drivingFiltration P hXV) τ := fun t => hfil t _ (hτ t)
    have hτlt : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < V ω := by
      filter_upwards [hτS, hSV] with ω ht hs using ht.1.trans_lt hs
    have hbig := hcl τ hτV hτlt
    refine ⟨hbig.1, ?_⟩
    let θ : Ω → ℝ≥0∞ := fun ω => min (τ ω : ℝ≥0∞) (S ω)
    let Z : Ω → HistorySpace nL nR := closedPrefixHistory xL xR ∘ killedHistory W VL VR θ
    have hZ : Measurable[hτ.measurableSpace] Z :=
      (measurable_closedPrefixHistory xL xR).comp (measurable_killedHistory_min_stopped hXS hτ)
    have hz : ∀ᵐ ω ∂P,
        Sec4.IsGoodStop (fun _ => (τ ω).untopD 0) W VL VR ζ ω ∧
        Z ω = Sec4.stopHistory (fun _ => (τ ω).untopD 0) (killedHistory W VL VR ζ ω) := by
      filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path, hτS, hτlt] with ω hp ht hlt
      have he := Coupling.coe_untopD_of_ne_top ht.2
      have htζ : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω :=
        he.trans_lt (hlt.trans_le (hC.2.1 ω))
      have hcont := (continuousOn_state_of_isSLEPathUpTo hp).mono
        (fun t h => lt_of_le_of_lt (ENNReal.coe_le_coe.2 h) htζ)
      have h0 : dState W VL VR ω 0 = initVal xL xR := by
        simp only [dState, initVal, hp.w_zero, Prod.mk.injEq, true_and]
        exact ⟨funext hp.vL_zero, funext hp.vR_zero⟩
      refine ⟨⟨htζ, hp.continuousOn_w, hp.continuousOn_vL, hp.continuousOn_vR⟩, ?_⟩
      exact closedPrefixHistory_killedHistory_eq
        (he.trans (min_eq_left ht.1).symm) hcont h0 htζ
    exact clauseAt_of_measurable_closedRecord (mΩ := mΩ) hC.2.2.1
      (Ito.measurableSpace_le_of_filtration_le hfil hτ hτV) hτV.measurableSpace_le hZ hz hbig.2
  · filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path, hSV] with ω hp hs T hT _
    have ht : (T : ℝ≥0∞) < ζ ω := hT.trans_lt (hs.trans_le (hC.2.1 ω))
    obtain ⟨r, hTr, hrζ⟩ := exists_between ht
    cases r with
    | top => exact (not_top_lt hrζ).elim
    | coe r =>
      refine ⟨r, ENNReal.coe_lt_coe.1 hTr, hp.continuousOn_w.mono ?_⟩
      intro t htr
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 htr) hrζ

end InteractingSLE.WFS
