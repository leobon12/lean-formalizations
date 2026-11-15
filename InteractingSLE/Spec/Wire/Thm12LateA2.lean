/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NowA2
import InteractingSLE.Spec.ZhanGT4.A1CanonStatement
import InteractingSLE.Spec.ZhanGT4.A1CoreStatement
import InteractingSLE.Spec.ZhanGT4.A2ImgEndMain
import InteractingSLE.Spec.Sec5.Lemma47AngleHit
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndHit
import InteractingSLE.Spec.Sec5.Prop51TgtNoWrap
import InteractingSLE.Spec.Sec5.Aux61R2Cover

/-! # A.2 fully discharged; Part A, Lemma 4.7 and target-component E1 -/

set_option autoImplicit false
noncomputable section
universe u

namespace InteractingSLE.Wire

/-- R76's rectangle statement supplies the G3 core used by the clearance adapters. -/
theorem late_coreG3
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ) :
    ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ :=
  fun κ => ZhanGT4.A1Core.a1DualCouplingG3CoreStatement_of_rect (hRect κ)

/-- R76's rectangle statement supplies the Eight core. -/
theorem late_coreEight
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ) :
    ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ :=
  fun κ => ZhanGT4.A1Core.a1DualCouplingEightCoreStatement_of_rect (hRectEight κ)

/-- A.3's G3 crosscut from the rectangle core of A.1 alone. -/
theorem late_fourForceCrosscutG3LifeStatement
    (hCore : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ) :
    ∀ κ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  fun κ => ZhanGT4.A2ImgEnd.fourForceCrosscutG3LifeStatement_of_refUA'
    (ZhanGT4.A1Canon.a1DualCouplingG3RefUAStatement_of_core (hCore κ))
    (ZhanGT4.A2P3ID.smallInHullG3Statement_of_pairContact' (ZhanGT4.A2X.P3.pairContactG3Statement κ))

/-- The Eight crosscut from the rectangle core of A.1 alone. -/
theorem late_threeForceCrosscutEightStatement
    (hCoreEight : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ) :
    ∀ κ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ :=
  fun κ => ZhanGT4.A2ImgEnd.threeForceCrosscutEightStatement_of_refUA'
    (ZhanGT4.A1Canon.a1DualCouplingEightRefUAStatement_of_core (hCoreEight κ))
    (ZhanGT4.A2P3ID.smallInHullEightStatement_of_pairContact' (ZhanGT4.A2X.P3.pairContactEightStatement κ))

/-- Clearance Part A from the two remaining rectangle cores. -/
theorem late_partAInputs
    (hCore : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ)
    (hCoreEight : ∀ κ, ZhanGT4.A1Canon.A1DualCouplingEightCoreStatement κ) :
    Sec5.PartAInputsSixteenDivOfClearance :=
  Sec5.partAInputsSixteenDivOfClearance_of_A2
    (late_fourForceCrosscutG3LifeStatement hCore) (late_threeForceCrosscutEightStatement hCoreEight)

/-- Lemma 4.7 at every source angle, from clearance Part A. -/
theorem late_lemma47QHitTStatement
    (hA : Sec5.PartAInputsSixteenDivOfClearance) {θ : ℝ}
    (hθ₁ : -(Real.pi / 2) < θ) (hθ₂ : θ < Real.pi / 2) :
    Sec5.RestartGen.Lemma47QHitTStatement.{u} θ :=
  Sec5.Lemma47Angle.lemma47QHitTStatement_of_partA_of_clearance hθ₁ hθ₂ hA

/-- Target-component E1 and Proposition 5.1 use the corrected reference fibre cover. -/
theorem late_prop51QStatement
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (Ref : ℝ → (ℝ → ℝ) → Finset ℝ → Set ℝ → Prop)
    (hCover : Sec5.Aux61R2.RefClockFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Ref)
    (hAvoid : ∀ κ b J I, Ref κ b J I → Sec5.Aux61Win.IsAvoidingRef.{u} κ b J I) :
    Sec5.Cond44Ref.Prop51QStatement.{u} := by
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  have hwin := Sec5.Aux61R2.restartWindowNullQOn_of_refClockCover hCover hAvoid
  exact Sec5.Prop51G.prop51QStatement_of_on Sec5.Prop51G.IsLargeGap
    (Sec5.Prop51H.prop51QOn_largeGap_of_partA_of_clearance hA)
    (Sec5.Prop51Tgt.prop51QOn_smallGap_of_tgt hreg
      (Sec5.Aux61Kernel.fwdNoEastCrosscutTgtQOn_of_window hreg hwin))

/-- The original right-angle first-contact input has no extra leaf. -/
theorem late_lemma47QHitStatement (hA : Sec5.PartAInputsSixteenDivOfClearance) :
    Sec5.Prop411Q.Lemma47QHitStatement.{u} :=
  Sec5.CrossRestart.KernelQ.lemma47QHitStatement_of_partA_of_clearance hA

end InteractingSLE.Wire
