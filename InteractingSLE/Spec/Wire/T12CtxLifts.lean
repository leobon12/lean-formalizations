/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12CtxSide
import InteractingSLE.Spec.Wire.T12Asm2Refs
import InteractingSLE.Spec.Sec7.SideC5Data
import InteractingSLE.Spec.Sec7.SideC6Clock

/-! # Visit lifts compatible with the assembly's installed references

Install the derivative lift of each actual original-time visit chart before
the assembly installs its reference hulls and records. The resulting data
are exactly the native visit-reference record, also after integerizing the
phase. No collar or boundary-height assertion is assumed here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec7.PocketWordIn Sec7.PocketStopSide Sec7.PocketTraversal
  Sec7.PocketStopWallsFin

/-- The actual visit-chart lifts at the assembly's rational original times.
All other analytic fields retain their supplied values. -/
def visitLifts {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) : SideTest Ω → Late.SideData Ω :=
  fun j => { side j with
    lift := fun r ω => (j.referenceVisitChart i d ω (SideTest.rationalOriginalTime r)).2.2 }

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)

/-- The exact side data read by ASSEMBLE2 after installing compatible lifts. -/
def installedSide (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) : SideTest Ω → Late.SideData Ω :=
  T12Asm.integerSide i
    (T12Asm2.refSide i x hS (visitLifts i (wordSafeObjects i x hS) side)
      SideTest.rationalOriginalTime) idx

/-- Installation and integerization commute with the native visit-reference
constructor. In particular the collar must use these installed hulls. -/
theorem installedSide_eq (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) :
    installedSide i x hS side idx = fun j =>
      ((side j).intPhase (16 / (16 / i.kappa)) (idx j)).withVisitReferences i j
        (wordSafeObjects i x hS) (counterflowObjects_measurable hS.counterflow)
        SideTest.rationalOriginalTime := rfl

/-- The actual installed fields: original hulls and records, visit lifts,
integer phase, and the unchanged common offset. -/
theorem installedSide_fields (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (j : SideTest Ω) :
    let d := wordSafeObjects i x hS
    let refs := installedSide i x hS side idx j
    refs.level = 0 ∧
      refs.sets = (fun r ω => regHull d.driver d.lifetime
        (SideTest.rationalOriginalTime r) ω) ∧
      refs.info = (fun r => j.originalReferenceInfo d
        (counterflowObjects_measurable hS.counterflow) (SideTest.rationalOriginalTime r)) ∧
      refs.lift = (fun r ω =>
        (j.referenceVisitChart i d ω (SideTest.rationalOriginalTime r)).2.2) ∧
      refs.phase = (fun q ω => (idx j q ω : ℝ) * PhaseSel.phaseStep (16 / (16 / i.kappa))) ∧
      refs.offset = (side j).offset := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The native chart compatibility holds on the actual live visit events. -/
theorem installedSide_referenceCharts (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ)
    (hRc : ∀ ω, Continuous (x.rightWall ω))
    (hLc : ∀ seed ω, Continuous (x.leftWall seed ω)) :
    let d := wordSafeObjects i x hS
    LateSideReferenceCharts i d (installedSide i x hS side idx)
      (fun j r ω => j.referenceVisitChart i d ω (SideTest.rationalOriginalTime r))
      (fun j q r => j.referenceVisitEvent i d (SideTest.rationalOriginalTime r) q) := by
  rw [installedSide_eq]
  exact visit_reference_charts i (wordSafeObjects i x hS)
    (fun j => (side j).intPhase (16 / (16 / i.kappa)) (idx j))
    (counterflowObjects_measurable hS.counterflow) (fun _ => SideTest.rationalOriginalTime)
    hRc hLc

/-- The lattice leaf uses the very same installed phase. -/
theorem installedSide_lattice (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) :
    LateSideLattice i (wordSafeObjects i x hS) (installedSide i x hS side idx) :=
  lateSideLattice_intPhase i (wordSafeObjects i x hS) _ idx

/-- The installed zero-time reference has the actual base-chart lift. -/
theorem installedSide_zero_lift (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) {j : SideTest Ω}
    (hj : j.Ready (wordSafeObjects i x hS)) {ω : Ω}
    (hω : ω ∈ (j.target i (wordSafeObjects i x hS)).event) :
    ∃ r : ℕ, SideTest.rationalOriginalTime r = 0 ∧
      (installedSide i x hS side idx j).lift r ω =
        ((j.target i (wordSafeObjects i x hS)).baseChart ω).2.2 := by
  refine ⟨Denumerable.eqv ℚ 0, ?_, ?_⟩
  · simpa only [Rat.cast_zero, Real.toNNReal_zero] using SideTest.rationalOriginalTime_eqv 0
  · change (j.referenceVisitChart i (wordSafeObjects i x hS) ω
      (SideTest.rationalOriginalTime (Denumerable.eqv ℚ 0))).2.2 = _
    rw [SideTest.rationalOriginalTime_eqv, Rat.cast_zero, Real.toNNReal_zero]
    exact SideTest.referenceVisitChart_zero_lift hj hω

end InteractingSLE.Wire.T12Ctx
