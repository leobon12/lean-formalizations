/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12CtxLifts
import InteractingSLE.Spec.Sec7.SideLCGauge

/-! # Integer phases and their actual mean probes after installation

For each samplewise integer choose the literal bounded-word capacity probes.
Read the integer index from this already lattice-valued version. Integerizing
and installing the references then preserve its phase and its probe identity.
This construction does not select the integer required by the collar heights.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec7.PocketWordIn Sec7.PocketStopSide Sec7.PocketTraversal Sec7.PhaseSel
  Sec7.Lemma71C

/-- The actual capacity probes of a samplewise constant integer phase.
The incoming side data retain the offset, visits and mean candidates. -/
def probeSide {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (n : SideTest Ω → Ω → ℤ) :
    SideTest Ω → Late.SideData Ω :=
  fun j => j.capacitySideData i d
    ((side j).intPhase (16 / (16 / i.kappa)) (fun _ => n j)) (n j)

/-- This chosen version is lattice-valued everywhere, including zero. -/
theorem probeSide_isIntPhase {Ω : Type} [MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω) (n : SideTest Ω → Ω → ℤ)
    (j : SideTest Ω) : (probeSide i d side n j).IsIntPhase (16 / (16 / i.kappa)) :=
  SideTest.isIntPhase_capacitySideData i d j _ (n j) (fun ω => ⟨n j ω, rfl⟩)

/-- Both the initial and positive-time values equal the selected integer. -/
theorem probeSide_phase {Ω : Type} [MeasurableSpace Ω] (i : BothLow)
    (d : WordObjects Ω) (side : SideTest Ω → Late.SideData Ω) (n : SideTest Ω → Ω → ℤ)
    (j : SideTest Ω) (q : ℝ≥0) (ω : Ω) :
    (probeSide i d side n j).phase q ω = (n j ω : ℝ) * phaseStep (16 / (16 / i.kappa)) := by
  change (j.capacitySideData i d _ _).phase q ω = _
  rw [SideTest.capacitySideData_phase]
  dsimp only [positiveLatticePhase, Late.SideData.intPhase]
  split_ifs <;> rfl

/-- The integer index of this version, used literally as `wordIdx`. -/
def probeIndex {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (n : SideTest Ω → Ω → ℤ) :
    SideTest Ω → ℝ≥0 → Ω → ℤ :=
  fun j => (probeSide i d side n j).latticeIndex (16 / (16 / i.kappa))

/-- Reading the index recovers the selected integer exactly. The step is
nonzero because the native parameter is the original parameter, above four. -/
theorem probeIndex_eq {Ω : Type} [MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (side : SideTest Ω → Late.SideData Ω) (n : SideTest Ω → Ω → ℤ)
    (j : SideTest Ω) (q : ℝ≥0) (ω : Ω) : probeIndex i d side n j q ω = n j ω := by
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  have hStep := phaseStep_ne_zero (hdual.symm ▸ i.kappa_gt_four)
  have h := (probeSide i d side n j).intPhase_latticeIndex_phase _
    (probeSide_isIntPhase i d side n j q ω)
  apply Int.cast_injective (α := ℝ)
  apply mul_right_cancel₀ hStep
  exact h.trans (probeSide_phase i d side n j q ω)

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)

/-- The exact integerization used by the assembly preserves the constructed
phase at every time and sample, rather than only at deterministic live times. -/
theorem installedProbeSide_phase (side : SideTest Ω → Late.SideData Ω)
    (n : SideTest Ω → Ω → ℤ) (j : SideTest Ω) (q : ℝ≥0) (ω : Ω) :
    let d := wordSafeObjects i x hS
    (installedSide i x hS (probeSide i d side n) (probeIndex i d side n) j).phase q ω =
      (probeSide i d side n j).phase q ω :=
  (probeSide i (wordSafeObjects i x hS) side n j).intPhase_latticeIndex_phase _
    (probeSide_isIntPhase i (wordSafeObjects i x hS) side n j q ω)

/-- The actual mean probes satisfy the native probe leaf for the same
installed references, visit lifts and integer phase. No continuity or
mean-probe identity is assumed. -/
theorem installedProbeSide_probes (side : SideTest Ω → Late.SideData Ω)
    (n : SideTest Ω → Ω → ℤ) {j : SideTest Ω}
    (hj : j.Ready (wordSafeObjects i x hS)) :
    let d := wordSafeObjects i x hS
    let target := j.target i d
    let refs := installedSide i x hS (probeSide i d side n) (probeIndex i d side n) j
    ∀ N : ℕ, ∀ᵐ ω ∂target.measure, ω ∈ target.event →
      let S := {t : ℝ≥0 | 0 < t ∧ (t : ℝ≥0∞) < capLife (target.curve ω) ∧
        t < (N : ℝ≥0) + 1}
      ContinuousOn (refs.probe N ω) S ∧ ContinuousOn (refs.baseProbe N ω) S ∧
        ContinuousOn (refs.weight N ω) S ∧
        ∀ t ∈ S, 0 < refs.weight N ω t ∧
          refs.probe N ω t - refs.baseProbe N ω t = refs.phase t ω * refs.weight N ω t := by
  intro d target refs N
  have h := j.capacitySideData_probes (i := i) hj
    ((side j).intPhase (16 / (16 / i.kappa)) (fun _ => n j)) (n j) N
  filter_upwards [h] with ω hω hA
  obtain ⟨hP, hB, hW, hEq⟩ := hω hA
  refine ⟨hP, hB, hW, fun t ht => ?_⟩
  obtain ⟨hPos, hDiff⟩ := hEq t ht
  refine ⟨hPos, ?_⟩
  change _ = (installedSide i x hS (probeSide i d side n) (probeIndex i d side n) j).phase
    t ω * _
  rw [installedProbeSide_phase]
  exact hDiff

end InteractingSLE.Wire.T12Ctx
