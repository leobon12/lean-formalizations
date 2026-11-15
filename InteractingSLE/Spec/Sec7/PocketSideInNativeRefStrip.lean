/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInZeroRefTimes
import InteractingSLE.Spec.Wire.Thm12NowPocket

/-!
# Original-time raw references from the actual strip system

PROVE-POCKET-SIDEIN. The strip's chosen counterflow supplies the retained
coupling and original filtration; its wall versions supply all wall laws.
Thus the native prefix, openness and raw-reference inputs are conclusions.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire

open Current Sec7 Sec7.PocketWordIn Sec7.PocketStop Sec7.PocketStopSide
  Sec7.PocketCoupling StripWall WholeField LocalSets
open Exist.Staged (IsRegularDriver)

/-- Install original-time references using the strip's actual chosen
counterflow witness. The input side data supply only the remaining fields. -/
def Now.originalReferenceSide {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (i : BothLow) (x : Now.StripObjects Ω) [IsProbabilityMeasure x.measure]
    (hS : StripSys.IsStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (side : SideTest Ω → Late.SideData Ω) (s : ℕ → ℝ≥0) :
    SideTest Ω → Late.SideData Ω :=
  fun j => (side j).withOriginalReferences j (Now.wordObjects i x hS)
    (counterflowObjects_measurable hS.counterflow) s

/-- The actual strip system proves the three native reference binders.
In particular no raw-reference, residual-increment or restart law is assumed.
The times are fixed original times, and the relative reference level is zero. -/
theorem now_originalReferenceSide_facts {Ω : Type} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (i : BothLow) (x : Now.StripObjects Ω)
    [IsProbabilityMeasure x.measure]
    (h44 : AdmCode.Theorem12ParamCond44Statement.{0})
    (hS : StripSys.IsStripSystem (16 / i.kappa) x.boundary x.jumps x.measure
      x.field x.driver x.lifetime x.experiment)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ x.jumps →
      x.boundary y + a * chiC (16 / i.kappa) ≤ -sleLambda (16 / i.kappa))
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ x.jumps →
      sleLambda (16 / i.kappa) ≤ x.boundary y + a * chiC (16 / i.kappa))
    (hθ₁ : x.thetaR ∈ Ioo (-(π / 2)) (π / 2))
    (hθ₂ : x.thetaL ∈ Ioc (-(π / 2)) (π / 2))
    (hr : ∀ j ω, IsRegularDriver (x.experiment (StripSys.alphaSpec x.thetaR) j ω))
    (hl : ∀ q : ℚ, 0 < q → ∀ j ω,
      IsRegularDriver (x.experiment (StripSys.betaSpec (StripSys.rt q) x.thetaL) j ω))
    (hu₀ : IsBoundedHarmonicExtension x.boundary x.jumps x.originalMean)
    (hvα : IsWallVersion x.measure (x.experiment (StripSys.alphaSpec x.thetaR)) 1 x.rightWall)
    (hvL : ∀ q, IsWallVersion x.measure
      (x.experiment (StripSys.betaSpec (StripSys.rt (positiveSeed q)) x.thetaL))
      (StripSys.rt (positiveSeed q)) (x.leftWall q))
    (side : SideTest Ω → Late.SideData Ω) (s : ℕ → ℝ≥0) :
    let d := Now.wordObjects i x hS
    ∀ j : SideTest Ω, j.Ready d →
      let target := j.target i d
      let refs := Now.originalReferenceSide i x hS side s j
      ∀ r, locPrefixSigma (refs.info r) target.event target.curve refs.level ≤ mΩ ∧
        (∀ ω ∈ target.event, IsOpen (H \ refs.sets r ω)) ∧
        PocketStopUnionLaw (refs.info r) target.measure target.event target.curve
          target.domain (refs.sets r) target.zeroField refs.level := by
  dsimp only
  let d := Now.wordObjects i x hS
  let : IsProbabilityMeasure d.measure := inferInstanceAs (IsProbabilityMeasure x.measure)
  have hdual : 16 / (16 / i.kappa) = i.kappa := by field_simp
  obtain ⟨hT, hTr, hC, hu'⟩ := counterflowObjects_spec hS.counterflow
  have hCoupling : IsOptionalHullCoupling i.kappa d.xL d.xR d.rhoL d.rhoR d.measure
      d.filtration d.driver d.forceL d.forceR d.brownian d.lifetime d.translatedField := by
    simpa only [d, Now.wordObjects, hdual] using hC
  have hMean : IsBoundedHarmonicExtension
      (forceBoundaryData i.kappa d.rhoL d.rhoR d.xL d.xR)
      (forceJumpSet d.xL d.xR) d.coupledMean := by
    simpa only [d, Now.wordObjects, hdual] using hu'
  have hw := fun q => wall_inputs h44 hS hleft hright (Ioo_subset_Icc_self hθ₁)
    (Ioc_subset_Icc_self hθ₂) (positiveSeed_pos q) hr (hl _ (positiveSeed_pos q)) hu₀ hvα (hvL q)
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

end InteractingSLE.Wire
