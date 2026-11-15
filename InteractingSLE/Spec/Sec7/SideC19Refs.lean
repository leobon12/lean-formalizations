/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC19Collar

/-! # The tops' reference leaves after the common R100 relift

PROVE-SIDE-COLLAR2. Relifting changes only the reference lifts.
The actual original-time sets, records, level and integer phase give
the same reference-law and lattice leaves used by the tops.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC19
open Wire Wire.Current LocalSets PocketStop PocketStopSide PocketTraversal PocketWordIn PocketCoupling
  PocketStopWallsFin

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)

/-- All installed fields, including the jointly relifted visit lifts. -/
theorem installedSideShift_fields (pre : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (m : SideTest Ω → Ω → ℤ) (j : SideTest Ω) :
    let d := wordSafeObjects i x hS
    let refs := SideC18.installedSideShift i x hS pre idx m j
    refs.level = 0 ∧
      refs.sets = (fun r ω => regHull d.driver d.lifetime
        (SideTest.rationalOriginalTime r) ω) ∧
      refs.info = (fun r => j.originalReferenceInfo d
        (counterflowObjects_measurable hS.counterflow) (SideTest.rationalOriginalTime r)) ∧
      refs.lift = (fun r ω z =>
        (j.referenceVisitChart i d ω (SideTest.rationalOriginalTime r)).2.2 z - 2 * π * m j ω) ∧
      refs.phase = (fun q ω => (idx j q ω : ℝ) * PhaseSel.phaseStep (16 / (16 / i.kappa))) ∧
      refs.offset = (pre j).offset := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The relifted references retain the installed integer phase. -/
theorem installedSideShift_lattice (pre : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (m : SideTest Ω → Ω → ℤ) :
    LateSideLattice i (wordSafeObjects i x hS) (SideC18.installedSideShift i x hS pre idx m) :=
  T12Ctx.installedSide_lattice i x hS pre idx

/-- The three tops' raw-reference leaves for the relifted installer:
prefix measurability, open complement and stopped-union law. -/
theorem physCtx_installedSideShift_referenceFacts
    {Ωw : BothLow → Type} [mWord : ∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (k : BothLow)
    (pre : SideTest (Ωw k) → Late.SideData (Ωw k))
    (idx : SideTest (Ωw k) → ℝ≥0 → Ωw k → ℤ) (m : SideTest (Ωw k) → Ωw k → ℤ) :
    let x := Relay.words T12Asm2.cond44Holds baseWord hWordb k
    let d := wordSafeObjects k x (hC.wordT k)
    ∀ j : SideTest (Ωw k), j.Ready d →
      let target := j.target k d
      let refs := SideC18.installedSideShift k x (hC.wordT k) pre idx m j
      ∀ r, locPrefixSigma (refs.info r) target.event target.curve refs.level ≤ mWord k ∧
        (∀ ω ∈ target.event, IsOpen (H \ refs.sets r ω)) ∧
        PocketStopUnionLaw (refs.info r) target.measure target.event target.curve
          target.domain (refs.sets r) target.zeroField refs.level :=
  T12Asm2.refSide_facts k (Relay.words T12Asm2.cond44Holds baseWord hWordb k)
    T12Asm2.cond44Holds (hC.wordT k) (hC.hWordleft k) (hC.hWordright k)
    (hC.hWordθ₁ k) (hC.hWordθ₂ k) (hC.hWordu₀ k) (hC.hWordvα k) (hC.hWordvL k)
    pre SideTest.rationalOriginalTime

end InteractingSLE.Sec7.SideC19
