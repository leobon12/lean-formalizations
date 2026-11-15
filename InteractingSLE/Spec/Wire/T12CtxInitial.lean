/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12CtxPhase
import InteractingSLE.Spec.Sec7.SideC7Mean
import InteractingSLE.Spec.Sec7.SideC6Initial

/-! # The installed zero-time collar from the initial mean formula

This conditional adapter isolates the initial mathematics for the literal
ASSEMBLE2 references. It excludes no physical landings: the exceptional set
is empty. The mean formula is an explicit input, not a source result proved
by this file. Its offset is unchanged by the installed integer phase.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec7.PocketWordIn Sec7.PocketCoupling

/-- Once the initial conditional mean has the canonical interior formula,
the native zero-time collar for the installed references needs no further
lift, phase, reference-law or germ hypothesis. -/
theorem installedSide_collarAtZero_of_meanFormula
    {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (side : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ)
    (G : SideTest Ω → Ω → DistOn upperHalfPlaneOpens)
    (hRc : ∀ ω, Continuous (x.rightWall ω))
    (hLc : ∀ seed ω, Continuous (x.leftWall seed ω))
    (hRm : ∀ t, Measurable fun ω => x.rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => x.leftWall seed ω t)
    (hFormula : InitialPocketMeanFormula i (wordSafeObjects i x hS) side G) :
    LateSideCollarAtExc i (wordSafeObjects i x hS) (installedSide i x hS side idx)
      (fun _ _ _ => ∅) 0 := by
  let d := wordSafeObjects i x hS
  let : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  let sideZ := fun j => (side j).intPhase (16 / (16 / i.kappa)) (idx j)
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  have hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField := by
    simpa only [d, wordSafeObjects, hdual] using
      (counterflowObjects_spec hS.counterflow).2.2.1
  have hHeight := initialReferenceHeightsExc_of_meanFormula i d sideZ G
    (counterflowObjects_measurable hS.counterflow) hRc hLc hRm hLm hCoupling hFormula
    (fun _ _ _ => ∅)
  rw [installedSide_eq]
  apply lateSideCollarAtZeroExc_of_initialReferenceHeights i d sideZ
    (counterflowObjects_measurable hS.counterflow) (fun _ => SideTest.rationalOriginalTime)
    (fun _ _ _ => ∅) _ hRc hLc hRm hLm hCoupling hHeight
  intro j
  refine ⟨Denumerable.eqv ℚ 0, ?_⟩
  simpa only [Rat.cast_zero, Real.toNNReal_zero] using SideTest.rationalOriginalTime_eqv 0

end InteractingSLE.Wire.T12Ctx
