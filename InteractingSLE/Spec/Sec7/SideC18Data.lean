/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC17ColCov
import InteractingSLE.Spec.Sec7.ColCovShiftCtx

/-! # R100's coupled phase index and relifted reference installer

PROVE-SIDE-COLLAR2. The offset is zero and the integer phase is
`1-n-lateCurPhaseInt`. Arbitrary offsets are not supplied.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC18
open Wire Wire.Current SideC17 PocketStopSide PocketStopField PhaseSel

theorem shiftChart_inv (c : Chart) (m : ℤ) : (shiftChart c m).2.1 = c.2.1 := rfl

/-- The phase index tied to the same branch as the relifted chart. -/
def frameIndex {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (n : SideTest Ω → Ω → ℤ) (j : SideTest Ω) (q : ℝ≥0) (ω : Ω) : ℤ :=
  1 - n j ω - ColCov.lateCurPhaseInt i d j q ω

/-- Zero-offset preliminary data with the required integer phase. -/
def frameSide {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (n : SideTest Ω → Ω → ℤ) (j : SideTest Ω) : Late.SideData Ω :=
  (zeroFramePreSide Ω).intPhase (16 / (16 / i.kappa)) (frameIndex i d n j)

theorem frameSide_offset {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (n : SideTest Ω → Ω → ℤ) (j : SideTest Ω) : (frameSide i d n j).offset = 0 := rfl

theorem frameSide_phase {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (n : SideTest Ω → Ω → ℤ) (j : SideTest Ω) (q : ℝ≥0) (ω : Ω) :
    (frameSide i d n j).phase q ω = chiC i.kappa *
      (2 * π * ((ColCov.lateCurPhaseInt i d j q ω : ℝ) - ((1 - n j ω : ℤ) : ℝ))) +
        (frameSide i d n j).offset := by
  have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
  change ((frameIndex i d n j q ω : ℤ) : ℝ) * phaseStep (16 / (16 / i.kappa)) = _ + 0
  simp only [frameIndex, phaseStep, hd, Int.cast_sub, Int.cast_one]
  ring

/-- Relift the reference lift while retaining all reference sets and
records and the chosen constant offset. -/
def reliftReferences {Ω : Type} (e : Late.SideData Ω) (m : Ω → ℤ) : Late.SideData Ω :=
  { e with lift := fun r ω z => e.lift r ω z - 2 * π * m ω }

/-- The R100 installer uses the actual original reference records and
the same measurable integer shift in each of their lifts. -/
def installedSideShift {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (pre : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ)
    (m : SideTest Ω → Ω → ℤ) (j : SideTest Ω) : Late.SideData Ω :=
  reliftReferences (T12Ctx.installedSide i x hS pre idx j) (m j)

end InteractingSLE.Sec7.SideC18
