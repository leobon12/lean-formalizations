/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.PartAClearanceA2
import InteractingSLE.Spec.ZhanGT4.A2TipSepWire
import InteractingSLE.Spec.ZhanGT4.A2Part3PCFin
import InteractingSLE.Spec.ZhanGT4.A2Part3IDExact
import InteractingSLE.Spec.Sec5.Prop51HGateNoWrap
import InteractingSLE.Spec.Sec5.Aux61KernelTop

/-! # R71–R74: canonical A.1, image endpoints, and the remaining target-component step -/

set_option autoImplicit false
noncomputable section
universe u

namespace InteractingSLE.Wire

/-- Parts 1 and 3 are proved. Only Canon and image endpoints
remain in this A.2 reduction. -/
theorem now_fourForceCrosscutG3LifeStatement
    (hCanon : ∀ κ, ZhanGT4.A1Ref.A1DualCouplingG3CanonStatement κ)
    (hEndpoint : ∀ κ, ZhanGT4.A2TipSep.ImageEndpointG3Statement.{0} κ)
    :
    ∀ κ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  ZhanGT4.A2TipSep.forall_fourForceCrosscutG3LifeStatement_of_refUA
    (fun κ => ZhanGT4.A1Ref.a1DualCouplingG3RefUAStatement_of_canon (hCanon κ))
    ZhanGT4.A2P1.a2SmallCrosscutG3Statement hEndpoint
    (fun κ => ZhanGT4.A2X.P3.smallInHullG3Statement_of_split (ZhanGT4.A2P3ID.imageDichotomyG3Statement κ)
      (ZhanGT4.A2X.P3.pairContactG3Statement κ))

/-- The Eight branch has the same remaining inputs. -/
theorem now_threeForceCrosscutEightStatement
    (hCanon : ∀ κ, ZhanGT4.A1Ref.A1DualCouplingEightCanonStatement κ)
    (hEndpoint : ∀ κ, ZhanGT4.A2TipSep.ImageEndpointEightStatement.{0} κ)
    :
    ∀ κ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ :=
  ZhanGT4.A2TipSep.forall_threeForceCrosscutEightStatement_of_refUA
    (fun κ => ZhanGT4.A1Ref.a1DualCouplingEightRefUAStatement_of_canon (hCanon κ))
    ZhanGT4.A2P1.a2SmallCrosscutEightStatement hEndpoint
    (fun κ => ZhanGT4.A2X.P3.smallInHullEightStatement_of_split (ZhanGT4.A2P3ID.imageDichotomyEightStatement κ)
      (ZhanGT4.A2X.P3.pairContactEightStatement κ))

/-- PROVE-PROP51-TGT's missing target-component corollary is explicit. The
window reduction supplies its E1 premise; no gate or bypass input remains. -/
theorem now_prop51QStatement_of_targetWindow
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hTarget : Sec5.Prop51G.FwdNoWrapQStatement →
      Sec5.Prop51Q.CfLineRegularQStatement.{u} →
      Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u} (fun _ _ _ => True) →
      Sec5.Cond44Ref.Prop51QStatement.{u})
    (hWindow : Sec5.Aux61Kernel.RestartWindowNullQOn.{u}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) :
    Sec5.Cond44Ref.Prop51QStatement.{u} := by
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  exact hTarget Sec5.Prop51HGate.fwdNoWrapQStatement hreg (Sec5.Aux61Kernel.fwdNoEastCrosscutTgtQOn_of_window_smallGap hreg hWindow)

end InteractingSLE.Wire
