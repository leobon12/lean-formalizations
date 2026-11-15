/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC18Installed

/-! # The complete R100 collar input, with no remaining mathematical input

PROVE-SIDE-COLLAR2. This successor exposes the current chart's relift;
the older `T12Asm3.SideCollarInputExc` still fixes its principal chart.
The source, shifted cover, increment laws and initial collar are proved.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC18
open Wire Wire.Current

/-- The tops' collar input in R100's explicit current and reference
frame. All offsets are zero and the integer shifts are walls-measurable.
This does not redefine the older principal-chart collar binder. -/
def SideCollarInputExcShift : Prop :=
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
        LateSideCollarExcShift i d (installedSideShift i x (hC.wordT i) (pre i) (idx i) (m i)) (m i) (X i)

/-- The proved relifted source input closes the complete relifted
collar input. No cover, wall, seed or increment-law hypothesis remains. -/
theorem sideCollarInputExcShift_of_source (hSrc : ColCovSourceInputShift) : SideCollarInputExcShift := by
  classical
  intro Ωw _ _ baseWord _ hWordb hC
  choose G₀ n hn _hSource hMean using hSrc Ωw baseWord hWordb hC
  let d := fun i => wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hC.wordT i)
  refine ⟨fun i _ => SideC17.zeroFramePreSide (Ωw i), fun i => frameIndex i (d i) (n i),
    fun i j ω => 1 - n i j ω, fun i => ColCov.colCovExc (d i),
    fun i j q ω => ColCov.colCovExc_finite _ j q ω, fun _ _ => rfl, ?_, ?_⟩
  · intro i _d j hj
    exact measurable_const.sub (hn i j hj)
  · intro i
    exact physCtx_collarShift_of_nativeMean hC i (G₀ i) (n i) (hMean i)

/-- The complete R100 collar input is proved without any remaining input. -/
theorem sideCollarInputExcShift_holds : SideCollarInputExcShift :=
  sideCollarInputExcShift_of_source colCovSourceInputShift_holds

end InteractingSLE.Sec7.SideC18
