/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.PartAClearanceA2
import InteractingSLE.Spec.ZhanGT4.A1DualStatement
import InteractingSLE.Spec.ZhanGT4.A2Part1Crosscut
import InteractingSLE.Spec.ZhanGT4.A2Part2
import InteractingSLE.Spec.ZhanGT4.A2Part3Split
import InteractingSLE.Spec.Sec5.Prop51HTopoDetourRegime

/-! # R70-safe A.2 and the finite-crosscut first-contact reduction -/

set_option autoImplicit false
noncomputable section
universe u

namespace InteractingSLE.Wire

/-- A.2 (G3) from the reference coupling and the remaining Parts 2 and 3. -/
theorem current_fourForceCrosscutG3LifeStatement
    (hA1 : ∀ κ : ℝ, ZhanGT4.A1Dual.A1DualCouplingG3RefStatement κ)
    (hSep : ∀ κ : ℝ, ZhanGT4.A2Part2.A2TipSepG3Statement.{u} κ)
    (hD : ∀ κ : ℝ, ZhanGT4.A2X.P3.ImageDichotomyG3Statement.{u} κ)
    (hContact : ∀ κ : ℝ, ZhanGT4.A2X.P3.PairContactG3Statement.{u} κ) :
    ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{u} κ :=
  ZhanGT4.A1Dual.forall_fourForceCrosscutG3LifeStatement_of_dualVer
    (fun κ => ZhanGT4.A1Dual.a1DualCouplingG3VerStatement_of_ref (hA1 κ))
    ZhanGT4.A2P1.a2SmallCrosscutG3Statement
    (ZhanGT4.A2Part2.forall_a2HullInsideG3Statement_of_tipSep hSep)
    (fun κ => ZhanGT4.A2X.P3.smallInHullG3Statement_of_split (hD κ) (hContact κ))

/-- A.2 (Eight) from the reference coupling and the remaining Parts 2 and 3. -/
theorem current_threeForceCrosscutEightStatement
    (hA1 : ∀ κ : ℝ, ZhanGT4.A1Dual.A1DualCouplingEightRefStatement κ)
    (hSep : ∀ κ : ℝ, ZhanGT4.A2Part2.A2TipSepEightStatement.{u} κ)
    (hD : ∀ κ : ℝ, ZhanGT4.A2X.P3.ImageDichotomyEightStatement.{u} κ)
    (hContact : ∀ κ : ℝ, ZhanGT4.A2X.P3.PairContactEightStatement.{u} κ) :
    ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ :=
  ZhanGT4.A1Dual.forall_threeForceCrosscutEightStatement_of_dualVer
    (fun κ => ZhanGT4.A1Dual.a1DualCouplingEightVerStatement_of_ref (hA1 κ))
    ZhanGT4.A2P1.a2SmallCrosscutEightStatement
    (ZhanGT4.A2Part2.forall_a2HullInsideEightStatement_of_tipSep hSep)
    (fun κ => ZhanGT4.A2X.P3.smallInHullEightStatement_of_split (hD κ) (hContact κ))

/-- First contact from the actual finite-excursion detour and eastern-side input.
The proved small-gap no-last-contact result removes the terminal bypass. -/
theorem current_cfFirstContactQStatement
    (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (hfinite : Sec5.Prop51HTopo.FiniteWesternCrosscutBypassStatement)
    (hside : Sec5.Prop51I.FwdPostContactEastSideQOn.{u}
      fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) :
    Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u} := by
  have hreg := Sec5.CfLineRegQ.cfLineRegularQStatement_of_partA_of_clearance hA
  apply Sec5.CfAvoidLeftQ.cfFirstContactQStatement_of_prop51Q hreg
  apply Sec5.Prop51G.prop51QStatement_of_on Sec5.Prop51G.IsLargeGap
    (Sec5.Prop51H.prop51QOn_largeGap_of_reg hreg)
  apply Sec5.Prop51HTopo.prop51QOn_smallGap_of_finiteCrosscutBypass hreg hfinite
  exact Sec5.Prop51G.fwdFirstContactNotEastQOn_of_split
    (Sec5.Prop51G.fwdFirstExitQOn_smallGap hreg)
    (Sec5.Prop51H.fwdPostContactQOn_of_residual hreg
      (Sec5.Prop51I.fwdPostContactEastQOn_of_side hreg hside))

end InteractingSLE.Wire
