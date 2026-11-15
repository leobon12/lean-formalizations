/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12CtxFamily
import InteractingSLE.Spec.Wire.T12AsmTop
import InteractingSLE.Spec.Sec7.R5PhaseTest
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefTimes

/-! # The context bounds for actual original-time side references

The source's references are the actual regularized counterflow hulls at the
canonical rational original times, with the walls and stopped driver as
marks. This normalizes supplied analytic side data, preserving their lift,
phase, offset, probes and visits. It proves the two context bounds; it does
not construct the analytic side data or assert the remaining collar law.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.T12Ctx

open Current Sec7 Sec7.PocketCoupling Sec7.PocketStopSide Sec7.PocketStopWallsFin

/-- Actual original-time reference sets and their complete retained records.
The analytic components of `e` are preserved. -/
abbrev referenceData {Ω : Type} [MeasurableSpace Ω] (d : WordObjects Ω)
    (j : SideTest Ω) (e : Late.SideData Ω)
    (hX : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime) : Late.SideData Ω :=
  e.withOriginalReferences j d hX SideTest.rationalOriginalTime

/-- The normalization keeps the reference lift and offset exactly. -/
theorem referenceData_analytic {Ω : Type} [MeasurableSpace Ω] (d : WordObjects Ω)
    (j : SideTest Ω) (e : Late.SideData Ω)
    (hX : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime) :
    (referenceData d j e hX).lift = e.lift ∧
    (referenceData d j e hX).phase = e.phase ∧
    (referenceData d j e hX).offset = e.offset :=
  e.withOriginalReferences_frame j d hX SideTest.rationalOriginalTime

/-- The `hSidepre` and `hSideFo` binders hold for these actual reference records
and hulls, also after the assembly's integer-phase substitution. -/
theorem side_context {Ω : Type} [mΩ : MeasurableSpace Ω] (i : BothLow) (d : WordObjects Ω)
    (hX : IsMeasurableKilledDriving d.driver d.forceL d.forceR d.lifetime)
    (e : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ)
    (hRm : ∀ t, Measurable fun ω => d.rightWall ω t)
    (hLm : ∀ seed t, Measurable fun ω => d.leftWall seed ω t) :
    ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d
      let refs := T12Asm.integerSide i (fun j => referenceData d j (e j) hX) idx j
      (∀ n, locPrefixSigma (refs.info n) target.event target.curve refs.level ≤ mΩ) ∧
      (∀ n ω, ω ∈ target.event → IsOpen (H \ refs.sets n ω)) := by
  intro j hj
  have hA : MeasurableSet[(j.target i d).walls] (j.target i d).event := by
    rw [SideTest.target_walls, SideTest.target_event]
    exact hj.2.2.2.2.2.2.2.1
  constructor
  · intro n
    have hWalls : (j.target i d).walls ≤ j.originalReferenceInfo d hX
        (SideTest.rationalOriginalTime n) := by
      rw [SideTest.target_walls]
      exact le_sup_left
    have hAm := hWalls _ hA
    change locPrefixSigma (j.originalReferenceInfo d hX (SideTest.rationalOriginalTime n))
      (j.target i d).event (j.target i d).curve 0 ≤ mΩ
    rw [locPrefixSigma_zero_of_driven hAm (SideTest.isDrivenCurve_target hj)]
    apply SideTest.originalReferenceInfo_le hX (s := SideTest.rationalOriginalTime n)
    intro k t
    fin_cases k
    · exact hRm t
    · exact hLm j.seed t
    · exact hLm j.seed t
  · intro n ω _
    exact R5Phase.isOpen_H_diff_regHull d.driver d.lifetime (SideTest.rationalOriginalTime n) ω

end InteractingSLE.Wire.T12Ctx
