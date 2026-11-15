/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC18Collar
import InteractingSLE.Spec.Sec7.R5EnlTwin

/-! # The positive collar in R100's frame

PROVE-SIDE-COLLAR2. The comparison germ uses the landed conditioned
increment laws and their original charts. Their maps are unchanged by
relifting. Both current and reference height lifts use the same shift.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC18
open Wire Wire.Current LocalSets PocketStopSide PocketStopField PocketStop PocketTraversal
  PocketCoupling PocketStopWallsFin Lemma71C Aux119Heights R5Enl

/-- The shifted height cover and the original conditioned increment laws
give the full positive collar in the shifted current frame. -/
theorem lateSideCollarPosExcShift_visitReferencesOn
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (m : SideTest Ω → Ω → ℤ)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hRc : ∀ ω, Continuous (d.rightWall ω)) (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hLife : ∀ᵐ ω ∂d.measure, d.lifetime ω = ⊤)
    (hLaw : LateSideIncrementLawsOn i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j))
      (fun j r ω => j.referenceVisitChart i d ω (s j r))
      (fun j q r => j.referenceVisitEvent i d (s j r) q))
    (hCover : ColCov.VisitReferenceHeightCoverPosExcShift i d side m s X) :
    ∀ q : ℝ≥0, 0 < q → LateSideCollarAtExcShift i d
      (fun j => reliftReferences ((side j).withVisitReferences i j d hKilled (s j)) (m j)) m X q := by
  intro q hqPos j hj
  unfold collarAtExcWithChart
  intro target refs zL zR gB hgB g hg
  have hMeasure : target.measure = d.measure := SideTest.target_measure j i d
  have hRef := visit_reference_charts i d side hKilled s hRc hLc
  have hSet := visit_references_liveExt (i := i) hj hKilled (side j) (s j)
  have hgB' : ∀ r, IsLocalSetMean (j.capacityReference i d (s j r)) target.zeroField d.measure (gB r) := by
    intro r
    have h := hgB r
    change IsLocalSetMean
      (liveExt target.event target.curve target.domain
        (((side j).withVisitReferences i j d hKilled (s j)).sets r)
        ((side j).withVisitReferences i j d hKilled (s j)).level) target.zeroField target.measure (gB r) at h
    rw [hMeasure, hSet r] at h
    exact h
  have hGerm := ae_all_iff.2 fun r => ae_physical_germ_of_old_chart_increment_law_on
    (P := d.measure) (M := j.referenceVisitEvent i d (s j r) q)
    (old := fun ω => j.referenceVisitChart i d ω (s j r))
    (current := relChart target.baseChart target.curve q) (gOld := gB r) (gNow := g)
    (fun ω hω => (hRef j hj q r ω hω).2.2.1)
    (fun ω hω => isConformal_relChart_of_driven (j.isDrivenCurve_target hj ω hω.1) hω.2.1
      (j.isConformal_baseChart_of_ready hj ω))
    (fun ω hω => (hRef j hj q r ω hω).2.2.2.1)
    (by simpa only [SideTest.target_measure] using hLaw j hj q gB hgB g hg r)
  have hHB := ae_all_iff.2 fun r => (hgB r).2.1
  rw [hMeasure] at hHB ⊢
  filter_upwards [hGerm, hHB, ae_regHull_eq hCoupling hLife, hCover j hj q hqPos gB hgB']
    with ω hGω hHBω hHull hAccess hA hq v hv hrep ξ hξ hX
  obtain ⟨r, x, ε, b, hVisit, hOrder, hε, hCollar, hTransition, hHeight, hWord⟩ :=
    hAccess hA hq ξ hξ hX
  have hMi : ω ∈ j.referenceVisitEvent i d (s j r) q :=
    ⟨hA, hq, hVisit, hOrder, hHull (s j r)⟩
  have hOld := j.isDomainChart_capacityReference_at_visit hj hRc (hLc j.seed)
    hA (s j r) hVisit (hHull (s j r))
  have hCur := j.isDomainChart_relChart_of_ready hj hRc (hLc j.seed) hA hq
  have hIncl := relChart_dom_antitone (j.isDomainChart_baseChart hj hRc (hLc j.seed) hA).1
    (j.isDrivenCurve_target hj ω hA) hq hOrder
  have hOldShift := SideC16.isDomainChart_shiftChart hOld (m j ω)
  have hRefHeight := tendsto_reference_height_at_incident_access hOldShift.1 hCur.1
    hIncl hTransition hHeight
  have hLift := j.tendsto_referenceVisit_lift_sub_zero hj hRc (hLc j.seed)
    hA hq hOrder hε hCollar hTransition
  refine ⟨r, b, 0, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hvB, hrepB⟩ := harmRep_spec (hHBω r)
    have hdomOld := (hRef j hj q r ω hMi).2.2.2.2
    have hdomCur := H_diff_activeCompl_eq_relChart_dom (c := target.baseChart) hA hq
      (j.isDrivenCurve_target hj ω hA) (j.isConformal_baseChart_of_ready (i := i) hj ω)
    have hvB' : InnerProductSpace.HarmonicOnNhd
        (harmRep (gB r ω) (H \ liveExt target.event target.curve target.domain (refs.sets r) refs.level ω))
        (j.referenceVisitChart i d ω (s j r)).dom := by
      rw [hdomOld]
      exact hvB
    have hrepB' : ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ (j.referenceVisitChart i d ω (s j r)).dom →
        gB r ω φ = ∫ z, harmRep (gB r ω)
          (H \ liveExt target.event target.curve target.domain (refs.sets r) refs.level ω) z * φ z := by
      rw [hdomOld]
      exact hrepB
    have hv' : InnerProductSpace.HarmonicOnNhd v (relChart target.baseChart target.curve q ω).dom := by
      rw [← hdomCur]
      exact hv
    have hrep' : ∀ φ : TestOn upperHalfPlaneOpens,
        tsupport φ ⊆ (relChart target.baseChart target.curve q ω).dom → g ω φ = ∫ z, v z * φ z := by
      rw [← hdomCur]
      exact hrep
    exact hGω r hMi _ v hvB' hrepB' hv' hrep' ξ x ε hε hCollar hTransition
  · rw [← hSet r] at hRefHeight
    exact hRefHeight
  · refine hLift.congr' (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [relChart_shift_lift]
    simp only [relChart_shift_inv]
    change (relChart target.baseChart target.curve q ω).2.2
        ((relChart target.baseChart target.curve q ω).2.1 z) -
        (j.referenceVisitChart i d ω (s j r)).2.2
          ((relChart target.baseChart target.curve q ω).2.1 z) =
      ((relChart target.baseChart target.curve q ω).2.2
          ((relChart target.baseChart target.curve q ω).2.1 z) - 2 * π * m j ω) -
        ((j.referenceVisitChart i d ω (s j r)).2.2
          ((relChart target.baseChart target.curve q ω).2.1 z) - 2 * π * m j ω)
    ring
  · simpa only [target, refs, zL, zR, reliftReferences, Late.SideData.withVisitReferences,
      Late.SideData.withOriginalReferences, mul_zero, add_zero] using hWord

end InteractingSLE.Sec7.SideC18
