/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSurviveIncrementGeometry

/-!
# Initial and current pocket references with both labels retained

PROVE-POCKET-SIDEIN. The full wall history at a fixed original time records
both the initial exterior and the current filling. The finite-wall union
law therefore gives the marked comparison law for these two different cuts.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Bornology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ LocalSets WholeField WangWu

/-- Both mean versions, local-set facts, pair-marked law and component
hypotheses for an actual pocket's initial and current original-time cuts. -/
theorem initial_current_reference_facts {Ω : Type} [mΩ : MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hj : j.Ready d)
    (hTransport : ∀ ω, IsChartTransport infinitySourceChart (-1) d.scale d.chartConstant
      (d.field ω) (d.chartField ω))
    (hTranslate : ∀ ω, IsTranslateAddConst 0 d.translateConstant (d.chartField ω) (d.translatedField ω))
    (hu : InnerProductSpace.HarmonicOnNhd d.originalMean H)
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField d.field d.originalMean) d.measure)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure d.filtration
      d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hu' : IsBoundedHarmonicExtension (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hCont : ∀ k ω, Continuous (pairWallFamily j j d k ω))
    (hStart : ∀ k ω, pairWallFamily j j d k ω 0 = 0)
    (hMeas : ∀ k t, Measurable fun ω => pairWallFamily j j d k ω t)
    (hDetermined : ∀ k t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily j j d k ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ k, Sec6.IsEntranceHistoryLocal (pairWallFamily j j d k)
      (centredField d.field d.originalMean) d.measure) (q : ℝ≥0) :
    let C := (j.target i d).domain
    let F := fun ω => regHull d.driver d.lifetime q ω
    let E0 := eventFilled j.event C (fun _ => ∅)
    let Eq := eventFilled j.event C F
    ∃ g0 gq : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean E0 (centredField d.translatedField d.coupledMean) d.measure g0 ∧
      IsLocalSetMean Eq (centredField d.translatedField d.coupledMean) d.measure gq ∧
      Measurable[mΩ, hittingSigma] E0 ∧ Measurable[mΩ, hittingSigma] Eq ∧
      IsLocalSet E0 (centredField d.translatedField d.coupledMean) d.measure ∧
      IsLocalSet Eq (centredField d.translatedField d.coupledMean) d.measure ∧
      IsHistoryAvoidanceLocal
        (MeasurableSpace.comap E0 hittingSigma ⊔ MeasurableSpace.comap Eq hittingSigma)
        (fun ω => E0 ω ∪ Eq ω) (centredField d.translatedField d.coupledMean) d.measure ∧
      (∀ᵐ ω ∂d.measure, ∀ p ∈ lowerUnion (E0 ω),
        ¬ IsBounded (connectedComponentIn (lowerUnion (E0 ω)) p)) ∧
      (∀ᵐ ω ∂d.measure, ∀ p ∈ lowerUnion (Eq ω),
        ¬ IsBounded (connectedComponentIn (lowerUnion (Eq ω)) p)) := by
  let F : Ω → Set ℂ := fun ω => regHull d.driver d.lifetime q ω
  let E0 := eventFilled j.event (j.target i d).domain (fun _ => ∅)
  let Eq := eventFilled j.event (j.target i d).domain F
  let ℋ := MeasurableSpace.comap (fullHist (pairWallFamily j j d)) inferInstance ⊔
    drivingFiltration d.measure hKilled q
  let ambient : MeasurableSpace Ω := mΩ
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hJoint := joint_walls_law_at_original_time hTransport hTranslate hu hh hCoupling hκ hu'
    hKilled hLife hCont hStart hMeas hDetermined hLocal q
  have hMarks : (j.target i d).walls ≤ ℋ := by
    rw [target_walls]
    exact wallsSigma_le_original_record hKilled
      (fun t => measurable_eval_fullHist hCont 0 t)
      (fun t => measurable_eval_fullHist hCont 1 t) q
  have hEvent : MeasurableSet[ℋ] j.event := by
    apply hMarks
    rw [target_walls]
    obtain ⟨-, -, -, -, -, -, -, hEvent, -⟩ := hj
    exact hEvent
  have hF : Measurable[ℋ, hittingSigma] F := by
    have hτ : IsStoppingTime (drivingFiltration d.measure hKilled)
        (fun _ : Ω => (q : WithTop ℝ≥0)) :=
      isStoppingTime_const (drivingFiltration d.measure hKilled) q
    have hStop := measurable_regHull_stopping hCoupling hκ hKilled hLife hτ
      (fun _ => WithTop.coe_ne_top)
    have hConst : hτ.measurableSpace = drivingFiltration d.measure hKilled q :=
      IsStoppingTime.measurableSpace_const (drivingFiltration d.measure hKilled) q
    rw [hConst] at hStop
    have hFq : Measurable[drivingFiltration d.measure hKilled q, hittingSigma] F := by
      simpa only [WithTop.untopD_coe] using hStop
    exact hFq.mono le_sup_right le_rfl
  have hRecord0 : Measurable[ℋ, hittingSigma] E0 :=
    measurable_eventFilled_of_ready hj (hCont 0) (hCont 1) hMarks hEvent
      (by rw [target_event]) measurable_const
  have hRecordq : Measurable[ℋ, hittingSigma] Eq :=
    measurable_eventFilled_of_ready hj (hCont 0) (hCont 1) hMarks hEvent
      (by rw [target_event]) hF
  have hBoth := retained_pair_law_of_joint_walls hRecordq hRecordq
    (fun ω hω _ => pairWallFamily_cover hj hj
      (by rwa [target_event]) (by rwa [target_event])) hJoint
  have hRetained : IsHistoryAvoidanceLocal ℋ Eq
      (centredField d.translatedField d.coupledMean) d.measure := by
    simpa only [union_self] using hBoth
  have hPair : IsHistoryAvoidanceLocal
      (MeasurableSpace.comap E0 hittingSigma ⊔ MeasurableSpace.comap Eq hittingSigma)
      (fun ω => E0 ω ∪ Eq ω) (centredField d.translatedField d.coupledMean) d.measure := by
    have hUnion : (fun ω => E0 ω ∪ Eq ω) = Eq := funext fun ω =>
      union_eq_right.2 (eventFilled_initial_subset j.event (j.target i d).domain F ω)
    rw [hUnion]
    exact IsHistoryAvoidanceLocal.mono_marks hRetained
      (sup_le hRecord0.comap_le hRecordq.comap_le)
  have hZero (ω : Ω) : regHull d.driver d.lifetime 0 ω = ∅ :=
    QuantumZipper.RS.fwdHull_zero_eq_empty
      ((continuous_regDrv d.driver d.lifetime ω).comp continuous_real_toNNReal)
  have hZeroFun : (fun ω => regHull d.driver d.lifetime 0 ω) = (fun _ => ∅) := funext hZero
  have hFacts0 := local_facts_at_original_time hj hTransport hTranslate hu hh hCoupling hu'
    hKilled hLife hCont hStart hMeas hDetermined hLocal 0
  rw [hZeroFun] at hFacts0
  obtain ⟨hm0, hl0, g0, hg0⟩ := hFacts0
  obtain ⟨hmq, hlq, gq, hgq⟩ := local_facts_at_original_time hj hTransport hTranslate hu hh hCoupling hu'
    hKilled hLife hCont hStart hMeas hDetermined hLocal q
  have hUnb := ae_eventFilled_unbounded_components hj (hCont 0) (hCont 1) hCoupling hLife
  have hUnb0 : ∀ᵐ ω ∂d.measure, ∀ p ∈ lowerUnion (E0 ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (E0 ω)) p) := by
    filter_upwards [hUnb] with ω hω
    simpa only [hZeroFun] using hω 0
  exact ⟨g0, gq, hg0, hgq, hm0, hmq, hl0, hlq, hPair, hUnb0, hUnb.mono fun _ hω => hω q⟩

end InteractingSLE.Wire.Current.SideTest
