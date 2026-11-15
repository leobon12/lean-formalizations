/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRetainCoupling
import InteractingSLE.Spec.Sec7.PocketSideInRetainGeometry

/-!
# The actual two-candidate marked law at original time

PROVE-POCKET-SIDEIN. Construct both records and their joint marked Gaussian
law from the ambient optional coupling and the three fixed walls' Lemma 6.2
inputs. Each pocket keeps its own candidate event. No conditional restart law,
nesting event, future witness or random relative clock is an input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ LocalSets WholeField WangWu

/-- The fixed actual candidates' pair-marked law is a consequence of the
existing ambient coupling and the determined local wall versions. The
normalizations are separate and the time is an original deterministic time. -/
theorem pair_marked_law_at_original_time {Ω : Type} [mΩ : MeasurableSpace Ω]
    {outer inner : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    [IsProbabilityMeasure d.measure] (hOuter : outer.Ready d) (hInner : inner.Ready d)
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
    (hCont : ∀ j ω, Continuous (pairWallFamily outer inner d j ω))
    (hStart : ∀ j ω, pairWallFamily outer inner d j ω 0 = 0)
    (hMeas : ∀ j t, Measurable fun ω => pairWallFamily outer inner d j ω t)
    (hDetermined : ∀ j t, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => pairWallFamily outer inner d j ω t) =ᵐ[d.measure]
        fun ω => f (centredField d.field d.originalMean ω))
    (hLocal : ∀ j, Sec6.IsEntranceHistoryLocal (pairWallFamily outer inner d j)
      (centredField d.field d.originalMean) d.measure) (q : ℝ≥0) :
    let F := fun ω => regHull d.driver d.lifetime q ω
    IsHistoryAvoidanceLocal
      (MeasurableSpace.comap (eventFilled outer.event (outer.target i d).domain F) hittingSigma ⊔
        MeasurableSpace.comap (eventFilled inner.event (inner.target i d).domain F) hittingSigma)
      (fun ω => eventFilled outer.event (outer.target i d).domain F ω ∪
        eventFilled inner.event (inner.target i d).domain F ω)
      (centredField d.translatedField d.coupledMean) d.measure := by
  let F : Ω → Set ℂ := fun ω => regHull d.driver d.lifetime q ω
  let ℋ := MeasurableSpace.comap (fullHist (pairWallFamily outer inner d)) inferInstance ⊔
    drivingFiltration d.measure hKilled q
  let ambient : MeasurableSpace Ω := mΩ
  have hκ : 0 < i.kappa := lt_trans (by norm_num) i.kappa_gt_four
  have hJoint := joint_walls_law_at_original_time hTransport hTranslate hu hh hCoupling hκ hu'
    hKilled hLife hCont hStart hMeas hDetermined hLocal q
  have hO : (outer.target i d).walls ≤ ℋ := by
    rw [target_walls]
    exact wallsSigma_le_original_record hKilled
      (fun t => measurable_eval_fullHist hCont 0 t)
      (fun t => measurable_eval_fullHist hCont 1 t) q
  have hI : (inner.target i d).walls ≤ ℋ := by
    rw [target_walls]
    exact wallsSigma_le_original_record hKilled
      (fun t => measurable_eval_fullHist hCont 0 t)
      (fun t => measurable_eval_fullHist hCont 2 t) q
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
  have hMO : MeasurableSet[ℋ] outer.event := by
    apply hO
    rw [target_walls]
    obtain ⟨-, -, -, -, -, -, -, hEventO, -⟩ := hOuter
    exact hEventO
  have hMI : MeasurableSet[ℋ] inner.event := by
    apply hI
    rw [target_walls]
    obtain ⟨-, -, -, -, -, -, -, hEventI, -⟩ := hInner
    exact hEventI
  have hRecordO := measurable_eventFilled_of_ready hOuter (hCont 0) (hCont 1) hO hMO
    (by rw [target_event]) hF
  have hRecordI := measurable_eventFilled_of_ready hInner (hCont 0) (hCont 2) hI hMI
    (by rw [target_event]) hF
  exact pair_marked_law_of_joint_walls hRecordO hRecordI
    (fun ω hωO hωI => pairWallFamily_cover hOuter hInner
      (by rwa [target_event]) (by rwa [target_event])) hJoint

end InteractingSLE.Wire.Current.SideTest
