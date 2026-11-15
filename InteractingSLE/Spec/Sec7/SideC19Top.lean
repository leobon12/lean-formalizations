/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC19Refs
import InteractingSLE.Spec.Sec7.SideC19Chart

/-! # The tops' collar input with current and references jointly relifted

PROVE-SIDE-COLLAR2 for PROVE-T12-ASSEMBLE5. C18 proves this collar
without remaining inputs. Here its clause has the tops' original
test-first order and explicitly supplies the current chart as well as
the installed original-time references in the same frame.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC19
open Wire Wire.Current

/-- The tops' collar input in R100's common current/reference frame.
The whole ready test is retained, the common offset is zero, and the
shift is walls-measurable. All capacities and admissible mean versions
occur in `LateSideCollarExcWithChart`. -/
def SideCollarInputExcRelift : Prop :=
  ∀ (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    (baseWord : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (baseWord i).measure]
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb),
    ∃ (pre : ∀ i, SideTest (Ωw i) → Late.SideData (Ωw i))
      (idx : ∀ i, SideTest (Ωw i) → ℝ≥0 → Ωw i → ℤ)
      (m : ∀ i, SideTest (Ωw i) → Ωw i → ℤ)
      (X : ∀ i, SideTest (Ωw i) → ℝ≥0 → Ωw i → Set ℂ),
      (∀ i j q ω, (X i j q ω).Finite) ∧ (∀ i j, (pre i j).offset = 0) ∧
      (∀ i, let d := wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hC.wordT i)
        ∀ j, j.Ready d → Measurable[(j.target i d).walls] (m i j)) ∧
      ∀ i, let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
        let d := wordSafeObjects i x (hC.wordT i)
        LateSideCollarExcWithChart i d
          (SideC18.installedSideShift i x (hC.wordT i) (pre i) (idx i) (m i))
          (fun j ω => PocketStopField.shiftChart ((j.target i d).baseChart ω) (m i j ω)) (X i)

/-- Adapt the proved C18 binder to the exact test-first collar used by
the tops, retaining all witnesses and their normalization properties. -/
theorem sideCollarInputExcRelift_of_shift (h : SideC18.SideCollarInputExcShift) :
    SideCollarInputExcRelift := by
  intro Ωw _ _ baseWord _ hWordb hC
  obtain ⟨pre, idx, m, X, hX, h0, hm, hCol⟩ := h Ωw baseWord hWordb hC
  refine ⟨pre, idx, m, X, hX, h0, hm, ?_⟩
  intro i
  exact (lateSideCollarExcWithChart_shift_iff _ _ _ _ _).2 (hCol i)

/-- The R100 collar binder for ASSEMBLE5, with no remaining input. -/
theorem sideCollarInputExcRelift_holds : SideCollarInputExcRelift :=
  sideCollarInputExcRelift_of_shift SideC18.sideCollarInputExcShift_holds

/-- The same result for direct use inside a tops' physical context.
Unpacking it provides the references, current chart, phase and finite
exceptions for every word index simultaneously. -/
theorem physCtx_exists_reliftedCollar
    {Ωw : BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) :
    ∃ (pre : ∀ i, SideTest (Ωw i) → Late.SideData (Ωw i))
      (idx : ∀ i, SideTest (Ωw i) → ℝ≥0 → Ωw i → ℤ)
      (m : ∀ i, SideTest (Ωw i) → Ωw i → ℤ)
      (X : ∀ i, SideTest (Ωw i) → ℝ≥0 → Ωw i → Set ℂ),
      (∀ i j q ω, (X i j q ω).Finite) ∧ (∀ i j, (pre i j).offset = 0) ∧
      (∀ i, let d := wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hC.wordT i)
        ∀ j, j.Ready d → Measurable[(j.target i d).walls] (m i j)) ∧
      ∀ i, let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
        let d := wordSafeObjects i x (hC.wordT i)
        LateSideCollarExcWithChart i d
          (SideC18.installedSideShift i x (hC.wordT i) (pre i) (idx i) (m i))
          (fun j ω => PocketStopField.shiftChart ((j.target i d).baseChart ω) (m i j ω)) (X i) :=
  sideCollarInputExcRelift_holds Ωw baseWord hWordb hC

end InteractingSLE.Sec7.SideC19
