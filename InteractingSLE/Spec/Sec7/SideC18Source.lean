/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC17ContextFrame

/-! # The R100 source input, with its actual relifted chart

PROVE-SIDE-COLLAR2. Original and transported native means are supplied
on every whole ready test. The branch is walls-measurable; the source
constant and counterflow offset are zero. No new mathematical input.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC18
open Wire Wire.Current LocalSets WholeField Aux119Heights SideC17

/-- R100's source data in the explicitly relifted frame, including their
proved physical native normalization. This has a distinct name from the
older principal-chart source input. -/
def ColCovSourceInputShift : Prop :=
  ∀ (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    (baseWord : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (baseWord i).measure]
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (i : BothLow),
    let d := wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hC.wordT i)
    ∃ (G₀ : SideTest (Ωw i) → Ωw i → DistOn upperHalfPlaneOpens)
      (n : SideTest (Ωw i) → Ωw i → ℤ),
      (∀ j, j.Ready d → Measurable[(j.target i d).walls] (n j)) ∧
      InitialPocketConjugateFlowMeanWithChart i d
        (fun j ω => zeroFrameChart ((j.target i d).baseChart ω) (n j ω)) G₀
        (fun j => j.canonicalInitialFlowMean i d) (fun _ _ => 1) (fun _ => 0) ∧
      ∀ j, j.Ready d →
        IsLocalSetMean (j.capacityReference i d 0) (j.target i d).zeroField d.measure
          (initialTransportedMeans i d G₀ j) ∧
        ∀ᵐ ω ∂d.measure, ω ∈ j.event → ∀ z ∈ (j.target i d).domain ω,
          harmRep (initialTransportedMeans i d G₀ j ω) (H \ j.capacityReference i d 0 ω) z +
              (j.target i d).harmonic z + chiC (j.target i d).kappa *
                (zeroFrameChart ((j.target i d).baseChart ω) (n j ω)).2.2 z =
            j.initialWordExtension i d ω (((j.target i d).baseChart ω).1 z)

/-- The relifted source input is supplied by the landed physical-context
theorem, with no remaining hypothesis. -/
theorem colCovSourceInputShift_holds : ColCovSourceInputShift := by
  intro Ωw _ _ baseWord _ hWordb hC i
  exact hC.exists_zeroFrame_initial_mean i

end InteractingSLE.Sec7.SideC18
