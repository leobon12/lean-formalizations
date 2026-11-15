/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ColCovTop
import InteractingSLE.Spec.Sec7.SideC16PhysicalLeft
import InteractingSLE.Spec.Sec7.SideC15Inverse

/-! # An original initial mean exists in every physical word context

PROVE-SIDE-COLLAR2. The landed raw reference law gives locality and a
counterflow mean. Inverse physical transport supplies the original mean.
No mean-existence or source-formula hypothesis enters the statement.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm3
open Current LocalSets WholeField Sec7 Sec7.SideC15 Sec7.SideC12 Sec7.StripWall Sec7.PocketStopSide
  Sec7.PocketWordIn

variable {Ωw : BothLow → Type} [∀ i, MeasurableSpace (Ωw i)] [∀ i, StandardBorelSpace (Ωw i)]
    {baseWord : ∀ i, Now.StripObjects (Ωw i)} [∀ i, IsProbabilityMeasure (baseWord i).measure]
    {hWordb : ∀ i, IsPiecewiseConstantBoundaryData (baseWord i).boundary (baseWord i).jumps}

/-- The actual original filled-pocket mean, on the whole ready test. -/
theorem PhysCtx.exists_initial_original_mean (hC : PhysCtx Ωw baseWord hWordb)
    (i : BothLow) (j : SideTest (Ωw i))
    (hj : j.Ready (wordSafeObjects i (Relay.words T12Asm2.cond44Holds baseWord hWordb i) (hC.wordT i))) :
    let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
    let d := wordSafeObjects i x (hC.wordT i)
    ∃ G₀ : Ωw i → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (fun ω => WangWu.negInv '' j.capacityReference i d 0 ω)
        (centredField d.field d.originalMean) d.measure G₀ := by
  let x := Relay.words T12Asm2.cond44Holds baseWord hWordb i
  let hS := hC.wordT i
  let d := wordSafeObjects i x hS
  let : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨hT, hTr, hCp, hu₁⟩ := counterflowObjects_spec hS.counterflow
  have hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField := by
    simpa only [d, wordSafeObjects, hd] using hCp
  have hu₁' : IsBoundedHarmonicExtension
      (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR) d.coupledMean := by
    simpa only [d, wordSafeObjects, hd] using hu₁
  have hreg := WordSafe.isTwoAngle_regTwo hS (hC.hWordleft i) (hC.hWordright i)
  have hw := fun q => WordSafe.wall_inputs T12Asm2.cond44Holds hreg
    (hC.hWordleft i) (hC.hWordright i) (Ioo_subset_Icc_self (hC.hWordθ₁ i))
    (Ioc_subset_Icc_self (hC.hWordθ₂ i)) (positiveSeed_pos q)
    (WordSafe.isRegularDriver_regTwo_twoAngle _ _ _) (WordSafe.isRegularDriver_regTwo_twoAngle _ _ _)
    (hC.hWordu₀ i)
    (WordSafe.isWallVersion_regTwo hS (hC.hWordleft i) (hC.hWordright i)
      StripSys.neg_pi_div_two_mem_Icc (Ioo_subset_Icc_self (hC.hWordθ₁ i)) (hC.hWordvα i))
    (WordSafe.isWallVersion_regTwo hS (hC.hWordleft i) (hC.hWordright i)
      StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self (hC.hWordθ₂ i)) (hC.hWordvL i q))
  obtain ⟨hcont, hstart, hmeas, hdet, hlocal⟩ := ColCov.pairWallFamily_facts d d.measure
    (centredField d.field d.originalMean)
    (hC.hWordvα i).continuous (fun q => (hC.hWordvL i q).continuous)
    (hC.hWordvα i).zero (fun q => (hC.hWordvL i q).zero)
    (hC.hWordvα i).measurable (fun q => (hC.hWordvL i q).measurable)
    (hw 1).1 (fun q => (hw q).2.2.1) (hw 1).2.1 (fun q => (hw q).2.2.2) j
  have hh := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff (hC.hWordu₀ i)
  obtain ⟨hm, _, hl⟩ := R5Same.initialReference_facts hj hT hTr (hC.hWordu₀ i).1 hh hCoupling hu₁'
    (counterflowObjects_measurable hS.counterflow) hS.lifetime hcont hstart hmeas hdet hlocal
  have hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens (j.target i d).zeroField d.measure := by
    rw [SideTest.target_zeroField]
    exact isZeroBoundaryGFF_centredField hCoupling hu₁'
  obtain ⟨g, hg⟩ := IsLocalSet.exists_isLocalSetMean hh₀ hm hl
  have hSet : eventFilled j.event (j.target i d).domain (fun _ => ∅) = j.capacityReference i d 0 := by
    rw [SideTest.capacityReference, SideTest.original_filling_zero]
  rw [hSet, SideTest.target_zeroField] at hg
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(π * chiC (16 / i.kappa)))
      (chiC i.kappa) (d.field ω) (d.chartField ω) := by
    simpa only [d, wordSafeObjects, hd] using hT
  have hTr' : ∀ ω, IsTranslateAddConst 0 0 (d.chartField ω) (d.translatedField ω) := by
    simpa only [d, wordSafeObjects, hd, zero_mul] using hTr
  exact ⟨_, localSetMean_inversePhysicalMean (j.original_filling_regular (i := i) hj 0)
    hT' hTr' (hC.hWordu₀ i).1 hu₁'.1 hg⟩

end InteractingSLE.Wire.T12Asm3
