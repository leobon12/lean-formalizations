/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1PatchStatement
import InteractingSLE.Spec.ZhanGT4.A1EightSeedGlue
import InteractingSLE.Spec.ZhanGT4.A1MultiMarkCanon
import InteractingSLE.Spec.ZhanGT4.A1SeedGeomFamily
import InteractingSLE.Spec.Sec5.Aux61FibKGlued
import InteractingSLE.Spec.Sec5.TwoMarkVersion6Clock
import InteractingSLE.Spec.Sec5.TwoMarkReference
import InteractingSLE.Spec.Sec5.CfConvConditional
import InteractingSLE.Spec.Sec5.RestartSwReg
import InteractingSLE.Spec.Sec7.PhaseSideR7
import InteractingSLE.Spec.Sec7.RefFrameTop
import InteractingSLE.Spec.Sec7.R7SurviveLoewner

/-!
# Current A.1, fibre-cover and restart adapters

PROVE-WIRE-PARTA. Conditional wrappers only; R80's patch/family obligations remain
explicit. The Eight seed input uses rectangle-dependent stopped records. The
reference cover uses the corrected fibres and the first-mark retargeting law.
-/

set_option autoImplicit false
noncomputable section
universe u

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire

/-- G3's rectangle law from the seeded-field/family assembly (R80). -/
theorem night_rectG3
    (hField : ∀ κ, ZhanGT4.A1Patch.A1DualCouplingG3FieldStatement κ) :
    ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ :=
  fun κ => ZhanGT4.A1Patch.a1DualCouplingG3RectStatement_of_field (hField κ)

/-- Eight's rectangle law with the corrected, rectangle-dependent seed records. -/
theorem night_rectEight
    (hSeed : ∀ κ, ZhanGT4.A1EightSeed.A1DualCouplingEightSeedMStatement κ) :
    ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ :=
  fun κ => ZhanGT4.A1EightSeed.a1DualCouplingEightRectStatement_of_seedM (hSeed κ)

/-- The actual dyadic fibres give the corrected reference-clock cover. -/
theorem night_refCover
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Sec5.Aux61R2.RefClockFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin :=
  Sec5.Aux61Cov.refClockFibreCoverOn_of_act (Sec5.Aux61Act.actFibreCoverOn_of_dy hDy)

/-- Proposition 5.1 through actual reference settings. Their injective stopped
traces are retained, as required by the negative-side two-mark law. -/
theorem night_prop51 (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hRetarget : Sec5.TwoMark.FirstMarkRetargetUpToStatement.{u}) :
    Sec5.Cond44Ref.Prop51QStatement.{u} := by
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  have htgt := Sec5.Aux61Act.fwdNoEastCrosscutTgtQOn_of_dyCover_refWin hreg hDy
    (Sec5.TwoMark.r5NegStatement_of_firstMarkRetargetUpTo hRetarget)
  apply Sec5.Prop51G.prop51QStatement_of_on Sec5.Prop51G.IsLargeGap
    (Sec5.Prop51H.prop51QOn_largeGap_of_partA_of_clearance hA)
  apply Sec5.Prop51Tgt.prop51QOn_smallGap_of_tgt hreg
  intro κ hκ hκ4 a b θ₁ θ₂ h12 _
  exact htgt κ hκ hκ4 a b θ₁ θ₂ h12 True.intro

/-- The switched-wall restart from the fixed-time chart law; all one-angle inputs
and the restricted Cond44 reference follow from Part A. -/
theorem night_switched (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hChart : Sec5.CfGiven.CfGivenChartStatement.{u}) :
    Sec5.RestartGen.SwitchedWallFirstHitStatement.{u} := by
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA
  exact Sec5.RestartSw.switchedWallFirstHitStatement_of_input h47
    (fun θ hθ => late_lemma47QHitTStatement hA hθ.1 hθ.2)
    (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411)
    (Sec5.CfGiven.counterflowGivenPrefixStatement_of_chart hChart)

end InteractingSLE.Wire
