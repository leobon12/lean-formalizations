/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC6Heights

/-!
# Initial native collar from the initial pocket's own heights

PROVE-SIDE-COLLAR2. Choose the original-zero reference. The comparison
limit is zero by equality of harmonic representatives. The inherited
lift difference is identically zero. Only the initial own-height input
remains mathematical; no increment law or interior visit at zero is used.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current Sec7 LocalSets Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C
  Sec7.PocketStopSide Sec7.Aux119Heights Sec7.PocketCoupling

/-- The exact initial native collar for the installed visit references,
conditional only on the initial own heights and the usual source data. -/
theorem lateSideCollarAtZeroExc_of_initialReferenceHeights
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (s : SideTest Ω → ℕ → ℝ≥0) (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ)
    (hZero : ∀ j, ∃ r, s j r = 0)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hHeight : InitialReferenceHeightsExc i d side X) :
    LateSideCollarAtExc i d
      (fun j => (side j).withVisitReferences i j d hKilled (s j)) X 0 := by
  intro j hj target refs zL zR gB hgB g hg
  obtain ⟨r, hr⟩ := hZero j
  have hRef := j.visit_reference_zero_eq (i := i) hj hRc (hLc j.seed) hKilled (side j) (s j) hr
  have hSet := j.activeCompl_zero_eq_capacityReference (i := i) hj hRc (hLc j.seed)
  have hMeasure : target.measure = d.measure := SideTest.target_measure j i d
  have hg₀ : IsLocalSetMean (j.capacityReference i d 0) target.zeroField d.measure (gB r) := by
    have h := hgB r
    rw [hMeasure, hRef.1, hSet] at h
    exact h
  rw [hMeasure] at hg ⊢
  have hMean := j.ae_initial_reference_eq hj hRc (hLc j.seed) hRm (hLm j.seed)
    hKilled hCoupling hg₀ hg
  have hHeight₀ := hHeight j hj (gB r) hg₀
  filter_upwards [hMean, hHeight₀] with ω hEq hHeightω hω hq v hv hrep ξ hξ hX
  have hEqv := hEq v (hSet ▸ hv) (hSet ▸ hrep)
  have hCurrent := j.isDomainChart_relChart_of_ready hj hRc (hLc j.seed) hω hq
  have hLift := hRef.2 ω hω
  let b := forceBoundaryData target.kappa target.rhoL target.rhoR
    (fun a => geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL a 0 ω -
      segDriver (target.curve ω) 0)
    (fun a => geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR a 0 ω -
      segDriver (target.curve ω) 0) ξ +
    refs.phase 0 ω * (Ioo
      (geomLW (fun t ω => segDriver (target.curve ω) t) target.marksL zL 0 ω -
        segDriver (target.curve ω) 0)
      (geomRW (fun t ω => segDriver (target.curve ω) t) target.marksR zR 0 ω -
        segDriver (target.curve ω) 0)).indicator 1 ξ - refs.offset
  refine ⟨r, b, 0, ?_, ?_, ?_, ?_⟩
  · refine (tendsto_const_nhds (x := (0 : ℝ))).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hDom : (relChart target.baseChart target.curve 0 ω).2.1 z ∈
        H \ j.capacityReference i d 0 ω := by
      rw [← hSet, ← hCurrent.2.1]
      exact mem_image_of_mem _ hz
    rw [hRef.1, hSet, hEqv hDom, sub_self]
  · refine (hHeightω hω ξ hξ hX).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hInv := relChart_zero_inv_of_driven (c := target.baseChart)
      (SideTest.isDrivenCurve_target hj ω hω) hz
    dsimp only [sideMean]
    rw [hRef.1, hSet, hLift, hInv]
    simp only [relChart, NNReal.coe_zero, Theorem14.GW2aCont.loewner_zero_lift]
    rfl
  · refine (tendsto_const_nhds (x := (0 : ℝ))).congr' (Eventually.of_forall fun z => ?_)
    rw [← hLift]
    exact (sub_self _).symm
  · dsimp only [b]
    rw [mul_zero, add_zero]

end InteractingSLE.Wire
