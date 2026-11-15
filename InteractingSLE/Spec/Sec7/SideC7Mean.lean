/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC7Extension

/-!
# Initial heights from one initial interior mean formula

PROVE-SIDE-COLLAR2. Uniqueness transfers the chosen initial mean formula
to arbitrary local-mean versions. The constructed bounded extension then
gives every non-jump boundary limit. The initial phase term vanishes.
The interior formula remains an explicitly named mathematical input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire

open Current LocalSets Sec7 Sec7.PocketStop Sec7.PocketStopSide Sec7.PocketTraversal
  Sec7.Aux119Heights

/-- One correctly normalized initial interior mean gives the initial
height requirement for all versions and every exceptional-set choice. -/
theorem initialReferenceHeightsExc_of_meanFormula
    {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    [IsProbabilityMeasure d.measure] (side : SideTest Ω → Late.SideData Ω)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hKilled : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ seed ω, Continuous (d.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t)
    (hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField)
    (hFormula : InitialPocketMeanFormula i d side G)
    (X : SideTest Ω → ℝ≥0 → Ω → Set ℂ) :
    InitialReferenceHeightsExc i d side X := by
  intro j hj target e zL zR g₀ hg₀
  obtain ⟨hG, hFormulaω⟩ := hFormula j hj
  have hSet := j.activeCompl_zero_eq_capacityReference (i := i) hj hRc (hLc j.seed)
  have hgCur := hg₀
  rw [← hSet] at hgCur
  have hEq := j.ae_initial_reference_eq hj hRc (hLc j.seed) hRm (hLm j.seed)
    hKilled hCoupling hG hgCur
  filter_upwards [hEq, hg₀.2.1, hFormulaω] with ω hEq hH hFormulaω hA ξ hξ _hX
  obtain ⟨hv₀, hrep₀⟩ := harmRep_spec hH
  have hEqv := hEq _ hv₀ hrep₀
  have hDriven := SideTest.isDrivenCurve_target hj ω hA
  have hBase := j.isDomainChart_baseChart hj hRc (hLc j.seed) hA
  have hCurrent := j.isDomainChart_relChart_of_ready hj hRc (hLc j.seed) hA
    (PocketPhaseMeans.capLife_pos hDriven)
  have hPhase := j.initial_phase_window_eq_zero hj hA ((side j).phase 0 ω) ξ
  rw [hPhase, add_zero]
  have hlim := ((j.isBoundedHarmonicExtension_initialWordExtension i d ω).2.2 ξ hξ).sub_const
    (side j).offset
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hInv := relChart_zero_inv_of_driven (c := target.baseChart) hDriven hz
  have hDom : (target.baseChart ω).2.1 z ∈ target.domain ω := by
    rw [← hBase.2.1]
    exact mem_image_of_mem _ hz
  have hComp : (target.baseChart ω).2.1 z ∈ H \ j.capacityReference i d 0 ω := by
    rw [← hSet, ← hCurrent.2.1, ← hInv]
    exact mem_image_of_mem _ hz
  dsimp only [sideMean]
  rw [hEqv hComp, hFormulaω hA _ hDom, hBase.fwd_inv hz]

end InteractingSLE.Wire
