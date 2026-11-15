/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovInstalled
import InteractingSLE.Spec.Wire.T12Asm3Final

/-!
# The tops' collar input `SideCollarInputExc` from the source input and the two shared inputs

Packet PROVE-COLLAR-COVER. The Theorem 1.2–1.3 tops (`Wire.T12Asm3.theorem12Statement_assembled3`,
`theorem13Statement_assembled3`) take the collar as `Wire.T12Asm3.SideCollarInputExc`. With the cover of this packet
(`ColCovAssembly`, `X = colCovExc`, finite) and the physical facts of every word context (as in
`T12Asm2.refSide_facts`), it reduces to three named inputs, each quantified over the physical word contexts and the
four indices:

* `ColCovSourceInput` (def, SIDE-COLLAR2's open source input, rulings R90/R90a): pre-side data with a lattice offset
  `m_j · phaseStep`, and `hSource`/`hBranch` of `Wire.lateSideCollarExc_originalReferences_of_conjugateMean_walls`
  (with `b = 0` the R90 offset is a lattice value, `sourceFrameOffset_zero_eq`);
* `ColCovSeedInput` (def, PROVE-R5-FRESHTIP): `LateSeedLand` of every word;
* `ColCovReflInput` (def, PROVE-WALL-ORDER): `LateOuterRefl` of every word with `X = colCovExc`;
* **`sideCollarInputExc_of_colCov`**: `SideCollarInputExc` from the three (integer phase `m_j − lateCurPhaseInt`,
  `X = colCovExc`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses; `T12Asm2.cond44Holds` is the R74-allowed `Theorem12ParamCond44Statement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest LocalSets WholeField PocketWordIn PhaseSel

/-- **SIDE-COLLAR2's source input in every word context** (named input; rulings R90/R90a): for every index, pre-side
data with a lattice offset, the original filled-pocket flow formula `hSource` and the branch compatibility `hBranch`
of `Wire.lateSideCollarExc_originalReferences_of_conjugateMean_walls`, for the word's objects. -/
def ColCovSourceInput : Prop :=
  ∀ (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    (baseWord : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (baseWord i).measure]
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (index : BothLow),
    ∃ (pre : SideTest (Ωw index) → Late.SideData (Ωw index)) (offsetIndex : SideTest (Ωw index) → ℤ)
      (G₀ : SideTest (Ωw index) → Ωw index → DistOn upperHalfPlaneOpens)
      (n : SideTest (Ωw index) → Ωw index → ℤ) (b : SideTest (Ωw index) → ℝ),
      (∀ j, (pre j).offset = (offsetIndex j : ℝ) * phaseStep (16 / (16 / index.kappa))) ∧
      InitialPocketConjugateFlowMean index
        (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)) G₀
        (fun j => j.canonicalInitialFlowMean index
          (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index))) n b ∧
      ∀ j : SideTest (Ωw index),
        j.Ready (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)) →
        ∀ᵐ ω ∂(wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
          (hC.wordT index)).measure,
          ω ∈ (j.target index (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index)
            (hC.wordT index))).event →
          (pre j).offset = b j + 2 * π * chiC (16 / index.kappa) * (1 - (n j ω : ℝ))

/-- **The seed-interval landings at the late pockets of every word** (named input, PROVE-R5-FRESHTIP's
`R5Fresh.R7SeedLand`). -/
def ColCovSeedInput : Prop :=
  ∀ (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    (baseWord : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (baseWord i).measure]
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (index : BothLow),
    LateSeedLand index
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index))

/-- **The outer collars' `K_s`-landing at the late pockets of every word** (named input, PROVE-WALL-ORDER's target
(3)), with the exceptional set `colCovExc`. -/
def ColCovReflInput : Prop :=
  ∀ (Ωw : BothLow → Type) [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    (baseWord : ∀ i, Now.StripObjects (Ωw i)) [∀ i, IsProbabilityMeasure (baseWord i).measure]
    (hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps)
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (index : BothLow),
    LateOuterRefl index
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index))
      (colCovExc (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)))

/-- **The tops' collar input from the source input and the two shared inputs** (`X = colCovExc`, finite; integer
phase `m_j − lateCurPhaseInt`). The physical facts of every word are read from the word context as in
`T12Asm2.refSide_facts` (walls' versions and the regularized-family wall inputs). -/
theorem sideCollarInputExc_of_colCov (hSrc : ColCovSourceInput) (hSeed : ColCovSeedInput)
    (hRefl : ColCovReflInput) : T12Asm3.SideCollarInputExc := by
  intro Ωw _ _ baseWord _ hWordb hC
  choose pre offsetIndex G₀ n b hOff hSource hBranch using hSrc Ωw baseWord hWordb hC
  refine ⟨pre, fun index j q ω => offsetIndex index j - lateCurPhaseInt index
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)) j q ω,
    fun index => colCovExc
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)),
    fun index j q ω => colCovExc_finite _ j q ω, fun index => ?_⟩
  have hS := hC.wordT index
  have hu₀ := hC.hWordu₀ index
  have hvα := hC.hWordvα index
  have hvL := hC.hWordvL index
  have hleft := hC.hWordleft index
  have hright := hC.hWordright index
  have hθ₁ := hC.hWordθ₁ index
  have hθ₂ := hC.hWordθ₂ index
  have hreg := Sec7.WordSafe.isTwoAngle_regTwo hS hleft hright
  have hw := fun q => Sec7.WordSafe.wall_inputs T12Asm2.cond44Holds hreg hleft hright
    (Ioo_subset_Icc_self hθ₁) (Ioc_subset_Icc_self hθ₂) (positiveSeed_pos q)
    (Sec7.WordSafe.isRegularDriver_regTwo_twoAngle _ _ _)
    (Sec7.WordSafe.isRegularDriver_regTwo_twoAngle _ _ _) hu₀
    (Sec7.WordSafe.isWallVersion_regTwo hS hleft hright
      StripSys.neg_pi_div_two_mem_Icc (Ioo_subset_Icc_self hθ₁) hvα)
    (Sec7.WordSafe.isWallVersion_regTwo hS hleft hright
      StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self hθ₂) (hvL q))
  have hHarm : EqOn (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).harmonic
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).coupledMean H := by
    intro z _
    show (Relay.words T12Asm2.cond44Holds baseWord hWordb index).harmonic z =
      (counterflowObjects hS.counterflow).mean z
    rw [hC.harmonic_eq index hS.counterflow]
  exact installedSide_lateSideCollarExc_colCov index _ hS (pre index) (offsetIndex index) (hOff index) (G₀ index)
    (n index) (b index) hu₀.1 (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀) hHarm
    hvα.continuous (fun q => (hvL q).continuous) hvα.measurable (fun q => (hvL q).measurable) hvα.zero
    (fun q => (hvL q).zero) (hC.hWordηm index) (hw 1).1 (fun q => (hw q).2.2.1) (hw 1).2.1 (fun q => (hw q).2.2.2)
    hS.lifetime (hSeed Ωw baseWord hWordb hC index) (hRefl Ωw baseWord hWordb hC index) (hSource index)
    (hBranch index)

end InteractingSLE.Sec7.ColCov
