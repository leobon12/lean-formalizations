/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovShift
import InteractingSLE.Spec.Sec7.ColCovSeed

/-!
# The relifted late cover for the words of the tops' physical context

Packet PROVE-COLLAR-COVER (third round). `visitReferenceHeightCoverPosExcShift_colCov` for a word of
`T12Asm3.PhysCtx` (`d = wordSafeObjects …`): every physical premise is read from the word context and its strip
system, and the seed-interval landings are PROVED (`noReturn_of_physCtx`, `lateSeedLand_of_noReturn`).

* **`physCtx_coverShift`**: the relifted cover (`X = colCovExc`, finite) from the relifted initial mean formula of every
  test and the phase condition in the relifted frame. For R100 take `m j ω = 1 − n j ω` (SIDE-COLLAR2's
  `SideC17.zeroFrameChart c n = shiftChart c (1 − n)`), offset `0` and the phase index `1 − n − lateCurPhaseInt`
  (phase `= χ·2π (lateCurPhaseInt − (1 − n))`).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.ColCov

open Wire Wire.Current Wire.Current.SideTest LocalSets WholeField Aux119Heights
open Wire.Current.SideTest (rationalOriginalTime)

/-- **The relifted late cover for a word of the tops' physical context** (`X = colCovExc`, finite; every reference
chart relifted by `−2π m`): see the module docstring. -/
theorem physCtx_coverShift {Ωw : BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}
    (hC : T12Asm3.PhysCtx Ωw baseWord hWordb) (index : BothLow)
    (side : SideTest (Ωw index) → Late.SideData (Ωw index)) (m : SideTest (Ωw index) → Ωw index → ℤ)
    (G : SideTest (Ωw index) → Ωw index → DistOn upperHalfPlaneOpens)
    (hG : let d := wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)
      ∀ j : SideTest (Ωw index), j.Ready d →
        IsLocalSetMean (j.capacityReference index d 0) (j.target index d).zeroField d.measure (G j))
    (hGform : let d := wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)
      ∀ j : SideTest (Ωw index), j.Ready d → ∀ᵐ ω ∂d.measure, ω ∈ (j.target index d).event →
        ∀ z ∈ (j.target index d).domain ω,
          harmRep (G j ω) (H \ j.capacityReference index d 0 ω) z + (j.target index d).harmonic z +
            chiC (j.target index d).kappa *
              (PocketStopField.shiftChart ((j.target index d).baseChart ω) (m j ω)).2.2 z =
            j.initialWordExtension index d ω (((j.target index d).baseChart ω).1 z) - (side j).offset)
    (hside : ∀ j q ω, (side j).phase q ω = chiC index.kappa * (2 * Real.pi * ((lateCurPhaseInt index
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)) j q ω : ℝ) -
        (m j ω : ℝ))) + (side j).offset) :
    VisitReferenceHeightCoverPosExcShift index
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index)) side m
      (fun _ => rationalOriginalTime)
      (colCovExc (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) (hC.wordT index))) := by
  have hS := hC.wordT index
  have : IsProbabilityMeasure
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).measure :=
    inferInstanceAs (IsProbabilityMeasure (Relay.words T12Asm2.cond44Holds baseWord hWordb index).measure)
  have hdual : 16 / (16 / index.kappa) = index.kappa := by
    have hk : index.kappa ≠ 0 := (lt_trans (by norm_num) index.kappa_gt_four).ne'
    field_simp
  obtain ⟨hT, hTr, hCc, hu'⟩ := PocketWordIn.counterflowObjects_spec hS.counterflow
  have hu₀ := hC.hWordu₀ index
  have hvα := hC.hWordvα index
  have hvL := hC.hWordvL index
  have hleft := hC.hWordleft index
  have hright := hC.hWordright index
  have hθ₁ := hC.hWordθ₁ index
  have hθ₂ := hC.hWordθ₂ index
  have hreg := Sec7.WordSafe.isTwoAngle_regTwo hS hleft hright
  have hw := fun q => Sec7.WordSafe.wall_inputs T12Asm2.cond44Holds hreg hleft hright
    (Ioo_subset_Icc_self hθ₁) (Ioc_subset_Icc_self hθ₂) (PocketWordIn.positiveSeed_pos q)
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
      (PocketWordIn.counterflowObjects hS.counterflow).mean z
    rw [hC.harmonic_eq index hS.counterflow]
  have hpw := pairWallFamily_facts
    (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS)
    (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).measure
    (centredField (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).field
      (wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS).originalMean)
    hvα.continuous (fun q => (hvL q).continuous) hvα.zero (fun q => (hvL q).zero) hvα.measurable
    (fun q => (hvL q).measurable) (hw 1).1 (fun q => (hw q).2.2.1) (hw 1).2.1 (fun q => (hw q).2.2.2)
  have hSeed := lateSeedLand_of_noReturn (i := index)
    (d := wordSafeObjects index (Relay.words T12Asm2.cond44Holds baseWord hWordb index) hS) hvα.continuous
    (fun q => (hvL q).continuous) (noReturn_of_physCtx hC index)
  exact visitReferenceHeightCoverPosExcShift_colCov index _ side m G hT hTr hu₀.1
    (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀)
    (by simpa only [wordSafeObjects, hdual] using hCc) (by simpa only [wordSafeObjects, hdual] using hu')
    (PocketWordIn.counterflowObjects_measurable hS.counterflow) hS.lifetime (fun j _ => (hpw j).1)
    (fun j _ => (hpw j).2.1) (fun j _ => (hpw j).2.2.1) (fun j _ => (hpw j).2.2.2.1) (fun j _ => (hpw j).2.2.2.2)
    hvα.continuous (fun q => (hvL q).continuous) hvα.measurable (fun q => (hvL q).measurable) hHarm
    (fun a => Theorem14.GW3Word.flowLineXL_nonpos _ _ a) (fun b => Theorem14.GW3Word.flowLineXR_nonneg _ _ b)
    hG hGform hSeed hside

end InteractingSLE.Sec7.ColCov
