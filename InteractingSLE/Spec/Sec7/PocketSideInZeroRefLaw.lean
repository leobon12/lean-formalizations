/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefRecord
import InteractingSLE.Spec.Sec7.PocketSideInInstGerm

/-!
# Raw references from the ambient optional coupling

PROVE-POCKET-SIDEIN. The fixed original-time wall-hull law gives the actual
filled reference with the intended walls and original driving history
retained. The zero-prefix result turns it into a raw stopped union law.
No conditional restart, residual increment or boundary-height law is assumed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStopWalls Sec7.PocketStopWallsFin
  Sec7.PocketWordPerQ Sec7.PocketCoupling Sec7.PocketStop LocalSets WholeField WangWu

/-- Both actual pocket shapes use the same centered ambient coupling field. -/
theorem target_zeroField {Ω : Type} [MeasurableSpace Ω] (j : SideTest Ω)
    (i : BothLow) (d : WordObjects Ω) :
    (j.target i d).zeroField = centredField d.translatedField d.coupledMean := by
  cases h : j.twoLeft <;> simp only [target, h, Bool.false_eq_true, ↓reduceIte]

/-- The raw-reference law is a conclusion of the ambient coupling and the
entrance-local, field-determined walls. The reference retains original time
`s` and is normalized at relative level zero. The complete retained filled
law is returned as well, before any later reference/collar selection. -/
theorem raw_reference_law_at_original_time {Ω : Type} [mΩ : MeasurableSpace Ω]
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
      (centredField d.field d.originalMean) d.measure) (s : ℝ≥0) :
    let F := fun ω => regHull d.driver d.lifetime s ω
    j.originalReferenceInfo d hKilled s ≤ mΩ ∧
      IsHistoryAvoidanceLocal (j.originalReferenceInfo d hKilled s)
        (eventFilled (j.target i d).event (j.target i d).domain F) (j.target i d).zeroField d.measure ∧
      PocketStopUnionLaw (j.originalReferenceInfo d hKilled s)
        d.measure (j.target i d).event (j.target i d).curve
        (j.target i d).domain F (j.target i d).zeroField 0 := by
  let F := fun ω => regHull d.driver d.lifetime s ω
  let full := MeasurableSpace.comap (fullHist (pairWallFamily j j d)) inferInstance ⊔
    drivingFiltration d.measure hKilled s
  let ambient : MeasurableSpace Ω := mΩ
  have hInfo := originalReferenceInfo_le hKilled hMeas s
  obtain ⟨hA, _, hRecord⟩ := original_reference_records hj hCoupling hKilled hLife hCont s
  have hJoint := joint_walls_law_at_original_time hTransport hTranslate hu hh hCoupling
    (lt_trans (by norm_num) i.kappa_gt_four) hu' hKilled hLife hCont hStart hMeas hDetermined hLocal s
  have hWalls : wallsSigma d.measure d.rightWall (d.leftWall j.seed) ≤ full :=
    wallsSigma_le_original_record (P := d.measure) hKilled
      (fun t => measurable_eval_fullHist hCont 0 t)
      (fun t => measurable_eval_fullHist hCont 1 t) s
  have hRetain : j.originalReferenceInfo d hKilled s ≤ full := sup_le hWalls le_sup_right
  have hFilled := retained_pair_law_of_joint_walls hRecord hRecord
    (fun ω hω _ => pairWallFamily_cover hj hj hω hω)
    (IsHistoryAvoidanceLocal.mono_marks hJoint hRetain)
  have hLaw : IsHistoryAvoidanceLocal (j.originalReferenceInfo d hKilled s)
      (eventFilled (j.target i d).event (j.target i d).domain F)
      (j.target i d).zeroField d.measure := by
    rw [target_zeroField]
    simpa only [union_self] using hFilled
  exact ⟨hInfo, hLaw, raw_reference_law_zero_of_retained hInfo hA
    (isDrivenCurve_target hj) hRecord hLaw⟩

end InteractingSLE.Wire.Current.SideTest
