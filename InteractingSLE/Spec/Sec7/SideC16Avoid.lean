/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.T12Asm2Inputs
/-! # The acyclic Prop. 4.11 input to initial pocket avoidance
PROVE-SIDE-COLLAR2. Use Part A and Lemma 4.7Q, as in the assembled tops.
-/
set_option autoImplicit false
namespace InteractingSLE.Wire.T12Ctx
/-- Prop. 4.11 from the already proved directional coupling laws. -/
theorem prop411_for_initial_pockets : Sec5.Cond44Ref.Prop411QStatement.{0} := by
  have hA := late_partAInputs
    (fun κ => Beacon.coreG3_of_lawC (T12Asm.g3Law T12Asm2.g3S T12Asm2.g3F κ))
    (fun κ => Beacon.coreEight_of_lawC (T12Asm.eightLaw T12Asm2.eightS κ))
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  exact Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA

end InteractingSLE.Wire.T12Ctx
