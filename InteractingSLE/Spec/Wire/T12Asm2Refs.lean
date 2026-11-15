/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12AsmTop
import InteractingSLE.Spec.Sec7.PocketSideInNativeRefStrip

/-! # Original-time side references on the two-angle word objects

PROVE-T12-ASSEMBLE2. PROVE-POCKET-SIDEIN's `Now.originalReferenceSide` installs fixed original-time
references in the word objects of a full strip system and proves the three raw-reference leaves. The
Theorem 1.2–1.3 tops read the word through `wordSafeObjects` of a **two-angle** strip system. This file
ports the installer and its proof to that interface. The walls' determination and entrance locality come
from `WordSafe.wall_inputs` on the regularized family, as in `T12AsmSide`; no regularity input is used.

* `refSide`: the installed side data (only `level`, `sets`, `info` change);
* `refSide_facts`: the prefix bound, open complements and raw stopped-union law, for every Ready test.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire.T12Asm2

open Current Sec7 Sec7.PocketWordIn Sec7.PocketStop Sec7.PocketStopSide
  Sec7.PocketCoupling StripWall WholeField LocalSets

/-- Original-time references installed in the two-angle word objects, using the strip's actual chosen
counterflow witness. The input side data supply every other field. -/
def refSide {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (side : SideTest Ω → Late.SideData Ω) (s : ℕ → ℝ≥0) :
    SideTest Ω → Late.SideData Ω :=
  fun j => (side j).withOriginalReferences j (wordSafeObjects i x hS)
    (counterflowObjects_measurable hS.counterflow) s

/-- **The raw-reference leaves hold for the installed references** on a two-angle strip system:
the prefix bound, the open complements and the raw stopped-union law, for every Ready test and
every reference index. The proof is `now_originalReferenceSide_facts` with the wall inputs of the
regularized two-angle family. -/
theorem refSide_facts {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (hS : Sec7.WordSafe.IsTwoAngleStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
    (hθ₁ : x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
    (hu₀ : IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
    (hvα : IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1 x.rightWall)
    (hvL : ∀ q, IsWallVersion x.measure
      (x.experiment (StripSys.betaSpec (StripSys.rt (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
    (side : SideTest Ω → Late.SideData Ω) (s : ℕ → ℝ≥0) :
    let d := wordSafeObjects i x hS
    ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d
      let refs := refSide i x hS side s j
      ∀ r, locPrefixSigma (refs.info r) target.event target.curve refs.level ≤ mΩ ∧
        (∀ ω ∈ target.event, IsOpen (H \ refs.sets r ω)) ∧
        PocketStopUnionLaw (refs.info r) target.measure target.event target.curve
          target.domain (refs.sets r) target.zeroField refs.level := by
  dsimp only
  let d := wordSafeObjects i x hS
  let : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨hT, hTr, hC, hu'⟩ := counterflowObjects_spec hS.counterflow
  have hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField := by
    simpa only [d, wordSafeObjects, hdual] using hC
  have hMean : IsBoundedHarmonicExtension
      (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean := by
    simpa only [d, wordSafeObjects, hdual] using hu'
  have hreg := Sec7.WordSafe.isTwoAngle_regTwo hS hleft hright
  have hw := fun q => Sec7.WordSafe.wall_inputs h44 hreg hleft hright
    (Ioo_subset_Icc_self hθ₁) (Ioc_subset_Icc_self hθ₂) (positiveSeed_pos q)
    (Sec7.WordSafe.isRegularDriver_regTwo_twoAngle _ _ _)
    (Sec7.WordSafe.isRegularDriver_regTwo_twoAngle _ _ _) hu₀
    (Sec7.WordSafe.isWallVersion_regTwo hS hleft hright
      StripSys.neg_pi_div_two_mem_Icc (Ioo_subset_Icc_self hθ₁) hvα)
    (Sec7.WordSafe.isWallVersion_regTwo hS hleft hright
      StripSys.pi_div_two_mem_Icc (Ioc_subset_Icc_self hθ₂) (hvL q))
  intro j hj
  apply original_references_facts hj hT hTr hu₀.1
    (Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hS.gff hu₀)
    hCoupling hMean (counterflowObjects_measurable hS.counterflow) hS.lifetime
  · intro k ω
    fin_cases k
    · exact hvα.continuous ω
    · exact (hvL j.seed).continuous ω
    · exact (hvL j.seed).continuous ω
  · intro k ω
    fin_cases k
    · exact hvα.zero ω
    · exact (hvL j.seed).zero ω
    · exact (hvL j.seed).zero ω
  · intro k t
    fin_cases k
    · exact hvα.measurable t
    · exact (hvL j.seed).measurable t
    · exact (hvL j.seed).measurable t
  · intro k t
    fin_cases k
    · exact (hw j.seed).1 t
    · exact (hw j.seed).2.2.1 t
    · exact (hw j.seed).2.2.1 t
  · intro k
    fin_cases k
    · exact (hw j.seed).2.1
    · exact (hw j.seed).2.2.2
    · exact (hw j.seed).2.2.2

end InteractingSLE.Wire.T12Asm2
