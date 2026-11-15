/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC18Source
import InteractingSLE.Spec.Sec7.SideC18Data

/-! # The exact shifted cover for the proved source witnesses

PROVE-SIDE-COLLAR2. Use COLLAR-COVER's landed producer at offset zero
and phase index `1-n-lateCurPhaseInt`. No cover for arbitrary real offsets
is asserted or assumed.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC18
open Wire Wire.Current LocalSets WholeField Aux119Heights

/-- The actual relifted native initial means give the finite positive
cover at the same branch and phase, with all geometric inputs discharged. -/
theorem physCtx_coverShift_zeroFrame
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
    let d := wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hC.wordT i)
    ColCov.VisitReferenceHeightCoverPosExcShift i d (frameSide i d n)
      (fun j ω => 1 - n j ω) (fun _ => SideTest.rationalOriginalTime) (ColCov.colCovExc d) := by
  let d := wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hC.wordT i)
  apply ColCov.physCtx_coverShift hC i (frameSide i d n) (fun j ω => 1 - n j ω)
    (initialTransportedMeans i d G₀) (fun j hj => (hMean j hj).1) ?_ (frameSide_phase i d n)
  dsimp only
  intro j hj
  simpa only [SideC17.zeroFrameChart, frameSide_offset, sub_zero, SideTest.target_event]
    using (hMean j hj).2

end InteractingSLE.Sec7.SideC18
