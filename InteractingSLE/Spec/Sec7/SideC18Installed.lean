/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC18Cover
import InteractingSLE.Spec.Sec7.SideC18Initial
import InteractingSLE.Spec.Sec7.SideC18Positive
import InteractingSLE.Spec.Sec7.SideC16Laws

/-! # The complete installed R100 collar in a physical context

PROVE-SIDE-COLLAR2. Combine the landed shifted positive cover, the
conditioned increment laws and the initial native mean. Both current
and reference lifts use `1-n`; offset zero and the phase are tied to it.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC18
open Wire Wire.Current LocalSets WholeField Aux119Heights PocketWordIn

/-- Every physical word has the complete installed relifted collar,
from its native initial means. All cover and increment inputs are proved. -/
theorem physCtx_collarShift_of_nativeMean
    {Ωw : BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (i : BothLow)
    (G₀ : SideTest (Ωw i) → Ωw i → DistOn upperHalfPlaneOpens)
    (n : SideTest (Ωw i) → Ωw i → ℤ)
    (hMean : let d := wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hC.wordT i)
      ∀ j, j.Ready d →
        IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure
          (initialTransportedMeans i d G₀ j) ∧
        ∀ᵐ ω ∂d.measure, ω ∈ j.event → ∀ z ∈ (j.target i d).domain ω,
          harmRep (initialTransportedMeans i d G₀ j ω) (H \ j.capacityReference i d 0 ω) z +
              (j.target i d).harmonic z + chiC (j.target i d).kappa *
                (SideC17.zeroFrameChart ((j.target i d).baseChart ω) (n j ω)).2.2 z =
            j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z)) :
    let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
    let d := wordSafeObjects i x (hC.wordT i)
    LateSideCollarExcShift i d
      (installedSideShift i x (hC.wordT i) (fun _ => SideC17.zeroFramePreSide (Ωw i))
        (frameIndex i d n) (fun j ω => 1 - n j ω))
      (fun j ω => 1 - n j ω) (ColCov.colCovExc d) := by
  let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
  let hS := hC.wordT i
  let d := wordSafeObjects i x hS
  let : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  let hKilled := counterflowObjects_measurable hS.counterflow
  let pre : SideTest (Ωw i) → Late.SideData (Ωw i) := fun _ => SideC17.zeroFramePreSide (Ωw i)
  let m : SideTest (Ωw i) → Ωw i → ℤ := fun j ω => 1 - n j ω
  have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
  have hCp : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField := by
    simpa only [d, wordSafeObjects, hd] using (counterflowObjects_spec hS.counterflow).2.2.1
  have hLaw := T12Ctx.installedFrameSide_incrementLawsOn i x hS
    (hC.hWordleft i) (hC.hWordright i) (hC.hWordθ₁ i) (hC.hWordθ₂ i) (hC.hWordu₀ i)
    (hC.hWordvα i) (hC.hWordvL i) (hC.hWordηm i) pre (frameIndex i d n) (fun _ => 0)
  have hLaw' : LateSideIncrementLawsOn i d
      (fun j => (frameSide i d n j).withVisitReferences i j d hKilled SideTest.rationalOriginalTime)
      (fun j r ω => j.referenceVisitChart i d ω (SideTest.rationalOriginalTime r))
      (fun j q r => j.referenceVisitEvent i d (SideTest.rationalOriginalTime r) q) := hLaw
  have hCov := physCtx_coverShift_zeroFrame hC i G₀ n hMean
  have hPos := lateSideCollarPosExcShift_visitReferencesOn i d (frameSide i d n) m hKilled
    (fun _ => SideTest.rationalOriginalTime) (ColCov.colCovExc d)
    (hC.hWordvα i).continuous (fun q => (hC.hWordvL i q).continuous) hCp hS.lifetime hLaw' hCov
  change LateSideCollarExcShift i d
    (fun j => reliftReferences
      ((frameSide i d n j).withVisitReferences i j d hKilled SideTest.rationalOriginalTime) (m j))
    m (ColCov.colCovExc d)
  intro q
  by_cases hq : q = 0
  · subst q
    intro j hj
    apply initialCollarAtZeroShift_of_meanFormula hj (frameSide i d n j) (m j) (ColCov.colCovExc d j)
      hKilled SideTest.rationalOriginalTime (Denumerable.eqv ℚ 0) SideTest.rationalOriginalTime_zero
      (hC.hWordvα i).continuous (hC.hWordvL i j.seed).continuous
      (hC.hWordvα i).measurable (hC.hWordvL i j.seed).measurable hCp (hMean j hj).1
    simpa only [SideC17.zeroFrameChart, m, frameSide_offset, sub_zero, SideTest.target_event]
      using (hMean j hj).2
  · exact hPos q (pos_iff_ne_zero.2 hq)

end InteractingSLE.Sec7.SideC18
