/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlLateInst
import InteractingSLE.Spec.Sec7.SideC14Install
import InteractingSLE.Spec.Wire.T12Asm2Refs

/-! # The landed increment laws on the actual normalized installer

PROVE-SIDE-COLLAR2. Reuse PROVE-R5-ENLARGED's law producer and the
regularized wall inputs already used by `T12Asm2.refSide_facts`.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Ctx
open Current Sec7 Sec7.PocketCoupling Sec7.StripWall Sec7.PocketWordIn Sec7.PocketStopSide
  WholeField

variable {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The actual installed visit references have the conditioned increment
laws, for every normalized offset and every integer phase. -/
theorem installedFrameSide_incrementLawsOn
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (hcumL : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hcumR : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
    (hθR : x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
    (hθL : x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
    (hu₀ : IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
    (hvR : IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1 x.rightWall)
    (hvL : ∀ q, IsWallVersion x.measure
      (x.experiment (StripSys.betaSpec (StripSys.rt (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
    (hηm : ∀ t : ℝ, 0 ≤ t → Measurable fun ω => x.curve ω t)
    (side : SideTest Ω → Late.SideData Ω) (idx : SideTest Ω → ℝ≥0 → Ω → ℤ)
    (a : SideTest Ω → ℝ) :
    let d := wordSafeObjects i x hS
    letI : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
    LateSideIncrementLawsOn i d (installedFrameSide i x hS side idx a)
      (fun j r ω => j.referenceVisitChart i d ω (SideTest.rationalOriginalTime r))
      (fun j q r => j.referenceVisitEvent i d (SideTest.rationalOriginalTime r) q) := by
  let d := wordSafeObjects i x hS
  let : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  have hd : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨hT, hTr, hC, hu₁⟩ := counterflowObjects_spec hS.counterflow
  have hC' : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField := by
    simpa only [d, wordSafeObjects, hd] using hC
  have hu₁' : IsBoundedHarmonicExtension
      (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR) (forceJumpSet d.xL d.xR) d.coupledMean := by
    simpa only [d, wordSafeObjects, hd] using hu₁
  have hreg := WordSafe.isTwoAngle_regTwo hS hcumL hcumR
  have hw := fun q => WordSafe.wall_inputs cond44 hreg hcumL hcumR
    (Ioo_subset_Icc_self hθR) (Ioc_subset_Icc_self hθL) (positiveSeed_pos q)
    (WordSafe.isRegularDriver_regTwo_twoAngle _ _ _)
    (WordSafe.isRegularDriver_regTwo_twoAngle _ _ _) hu₀
    (WordSafe.isWallVersion_regTwo hS hcumL hcumR
      StripSys.neg_pi_div_two_mem_Icc (Ioo_subset_Icc_self hθR) hvR)
    (WordSafe.isWallVersion_regTwo hS hcumL hcumR
      StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self hθL) (hvL q))
  change LateSideIncrementLawsOn i d
    (fun j => (((normalizeInitialOffset side a j).intPhase (16 / (16 / i.kappa)) (idx j)).withVisitReferences
      i j d (counterflowObjects_measurable hS.counterflow) SideTest.rationalOriginalTime)) _ _
  exact lateSideIncrementLawsOn_visitReferences i d _ (counterflowObjects_measurable hS.counterflow)
    (fun _ => SideTest.rationalOriginalTime) hT hTr hu₀.1
    (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀) hC' hu₁' hS.lifetime
    hvR.measurable (fun q => (hvL q).measurable) hvR.continuous (fun q => (hvL q).continuous)
    hvR.zero (fun q => (hvL q).zero) hηm
    (hw 1).1 (fun q => (hw q).2.2.1) (hw 1).2.1 (fun q => (hw q).2.2.2)

end InteractingSLE.Wire.T12Ctx
