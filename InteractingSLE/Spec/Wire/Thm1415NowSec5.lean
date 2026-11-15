/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndHit
import InteractingSLE.Spec.Sec5.Prop51TgtNoWrap

/-! # The Section 5 inputs of Theorem 1.5 from Part A and target-component (E1) -/

set_option autoImplicit false
noncomputable section
universe u
namespace InteractingSLE.Wire

/-- Lemma 4.7Q and the counterflow exit theorem now supply Proposition 4.11Q. -/
theorem prop411QStatement_of_partA_clearance_now
    (hA : Sec5.PartAInputsSixteenDivOfClearance) : Sec5.Cond44Ref.Prop411QStatement.{u} :=
  Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance
    (Sec5.CrossRestart.KernelQ.lemma47QHitStatement_of_partA_of_clearance hA) hA

/-- The landed target-component no-wrap theorem uses only counterflow regularity
from Part A. No western bypass or unrestricted post-contact assertion is needed. -/
theorem prop51QStatement_of_partA_clearance_of_target_now
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (htgt : Sec5.Aux61Kernel.FwdNoEastCrosscutTgtQOn.{u}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) : Sec5.Cond44Ref.Prop51QStatement.{u} := by
  have hreg : Sec5.Prop51Q.CfLineRegularQStatement.{u} :=
    Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  exact Sec5.Prop51G.prop51QStatement_of_on Sec5.Prop51G.IsLargeGap
    (Sec5.Prop51H.prop51QOn_largeGap_of_reg hreg)
    (Sec5.Prop51Tgt.prop51QOn_smallGap_of_tgt hreg htgt)

end InteractingSLE.Wire
