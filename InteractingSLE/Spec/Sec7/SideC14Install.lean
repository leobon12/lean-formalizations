/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC14Offset
import InteractingSLE.Spec.Wire.T12CtxLifts

/-!
# The installed original-time references with R90's frame offset

PROVE-SIDE-COLLAR2. The installer now writes the initial frame offset
alongside the reference sets, level and information. Its visit-chart
lifts and integer phases are those already proved for the assembly.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec7.PocketStopSide Sec7.PocketWordIn Sec7.PocketStopWallsFin

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)

/-- R90's installed side data: actual references and their records,
compatible visit lifts, integer phases, and the source frame's offset. -/
def installedFrameSide (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (a : SideTest Ω → ℝ) :
    SideTest Ω → Late.SideData Ω :=
  normalizeInitialOffset (installedSide i x hS side idx) a

/-- Normalizing before the reference/phase installation gives exactly
the same side data. Hence all existing reference proofs apply literally. -/
theorem installedFrameSide_eq (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (a : SideTest Ω → ℝ) :
    installedFrameSide i x hS side idx a =
      installedSide i x hS (normalizeInitialOffset side a) idx := rfl

/-- Every installed field, including the newly normalized common offset. -/
theorem installedFrameSide_fields (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (a : SideTest Ω → ℝ) (j : SideTest Ω) :
    let d := wordSafeObjects i x hS
    let refs := installedFrameSide i x hS side idx a j
    refs.level = 0 ∧
      refs.sets = (fun r ω => regHull d.driver d.lifetime
        (SideTest.rationalOriginalTime r) ω) ∧
      refs.info = (fun r => j.originalReferenceInfo d
        (counterflowObjects_measurable hS.counterflow) (SideTest.rationalOriginalTime r)) ∧
      refs.lift = (fun r ω =>
        (j.referenceVisitChart i d ω (SideTest.rationalOriginalTime r)).2.2) ∧
      refs.phase = (fun q ω => (idx j q ω : ℝ) * PhaseSel.phaseStep (16 / (16 / i.kappa))) ∧
      refs.offset = a j := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The old reference-chart theorem holds for the normalized installer. -/
theorem installedFrameSide_referenceCharts (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (a : SideTest Ω → ℝ)
    (hRc : ∀ ω, Continuous (x.rightWall ω))
    (hLc : ∀ seed ω, Continuous (x.leftWall seed ω)) :
    let d := wordSafeObjects i x hS
    LateSideReferenceCharts i d (installedFrameSide i x hS side idx a)
      (fun j r ω => j.referenceVisitChart i d ω (SideTest.rationalOriginalTime r))
      (fun j q r => j.referenceVisitEvent i d (SideTest.rationalOriginalTime r) q) := by
  rw [installedFrameSide_eq]
  exact installedSide_referenceCharts i x hS (normalizeInitialOffset side a) idx hRc hLc

/-- Integer phase quantization is compatible with the installed offset. -/
theorem installedFrameSide_lattice (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (a : SideTest Ω → ℝ) :
    LateSideLattice i (wordSafeObjects i x hS) (installedFrameSide i x hS side idx a) := by
  rw [installedFrameSide_eq]
  exact installedSide_lattice i x hS (normalizeInitialOffset side a) idx

/-- The source branch compatibility is true for the installed data by
construction, with the initial frame's branch on each test. -/
theorem installedFrameSide_branch (side : SideTest Ω → Late.SideData Ω)
    (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) (b : SideTest Ω → ℝ) (n : SideTest Ω → ℤ) :
    ∀ j : SideTest Ω, j.Ready (wordSafeObjects i x hS) → ∀ᵐ ω ∂x.measure,
      ω ∈ (j.target i (wordSafeObjects i x hS)).event →
        (installedFrameSide i x hS side idx
          (fun j => sourceFrameOffset (16 / i.kappa) (b j) (n j)) j).offset =
          b j + 2 * Real.pi * QuantumZipper.chiC (16 / i.kappa) * (1 - (n j : ℝ)) :=
  fun _ _ => ae_of_all _ fun _ _ => rfl

/-- The initial frame reads only the offset from the side data; its
proved identity therefore holds for the literal normalized references. -/
theorem installedFrameSide_initialFrame
    {frameSide : SideTest Ω → Late.SideData Ω}
    {G : SideTest Ω → Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {M : SideTest Ω → Ω → ℂ → ℝ}
    (hFrame : InitialPocketFlowFrame i (wordSafeObjects i x hS) frameSide G M)
    (side : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ) :
    InitialPocketFlowFrame i (wordSafeObjects i x hS)
      (installedFrameSide i x hS side idx (fun j => (frameSide j).offset)) G M :=
  hFrame.normalize_offset _

end InteractingSLE.Wire.T12Ctx
