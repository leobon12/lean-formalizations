/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12NightExpanded
import InteractingSLE.Spec.ZhanGT4.A1G3CalcStatement
import InteractingSLE.Spec.Sec5.CfResumeIntegrable
import InteractingSLE.Spec.Sec7.OuterInWire

/-!
# Seeded G3, image-field moments and the outer-pocket reductions

PROVE-WIRE-PARTA. These adapters retain the actual reference-setting route to
Proposition 5.1. The outer determination law is shared with the extremal pockets
and Lemma 7.25; it is not a new hypothesis.
-/

set_option autoImplicit false
noncomputable section
universe u
open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (chiC)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Wire
open Sec7 Sec7.R7Leaves Sec7.RefWire

/-- The seeded mixed-mark G3 construction supplies the previous field-law leaf. -/
theorem dawn_fieldG3
    (hSeedG : ∀ κ, ZhanGT4.A1G3Calc.A1DualCouplingG3SeedGStatement κ) :
    ∀ κ, ZhanGT4.A1Patch.A1DualCouplingG3FieldStatement κ :=
  fun κ => ZhanGT4.A1G3Calc.a1DualCouplingG3FieldStatement_of_seedG (hSeedG κ)

/-- Image-field integrability is discharged by the landed random-word moment bound. -/
theorem dawn_chartIntegrable (hA : Sec5.PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : Night.ConvertedIntegrableOn.{u} := by
  intro κ b J Ω mΩ hSB P hP h W ζ hκ hκ4 hb hh hcf hζ hleft hright θ hθ D hDm hDreg hD s hs η hη φ
  exact Sec5.CfResume.integrable_imgField_recOf_of_strip hh.1 hA href hκ hκ4 hb hcf hζ
    hleft hright hθ hDm hDreg hD s hη φ

/-- The outer completion from the remaining per-configuration geometry and phase data. -/
theorem dawn_outerCompletion
    (hRect : ∀ κ, ZhanGT4.A1Core.A1DualCouplingG3RectStatement κ)
    (hRectEight : ∀ κ, ZhanGT4.A1Core.A1DualCouplingEightRectStatement κ)
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hRetarget : Sec5.TwoMark.FirstMarkRetargetUpToStatement.{0})
    (hQ : Sec5.FrameQ.QScheduleFirstHitStatement.{0})
    (hlaws : Hsd.Fig51CandLawsStatement
      (late_theorem12ParamCond44Statement (late_coreG3 hRect) (late_coreEight hRectEight)))
    (hgeom : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterIn.R7OuterGeomRemaining.{0} k rL rR)
    (hside : ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR → k / 2 - 4 < max rL rR →
      OuterIn.R7OuterPhaseSideRemaining.{0} k rL rR) :
    ∀ k : ℝ, 4 < k → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      k / 2 - 4 < max rL rR → OuterPocketCompletion.{0} k rL rR := by
  have hA := late_partAInputs (late_coreG3 hRect) (late_coreEight hRectEight)
  have h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0} := late_lemma47QHitStatement hA
  have h411 := Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance h47 hA
  have h51 := night_prop51 hA hDy hRetarget
  have hFH := Sec5.FrameQ.stagedPrefixFirstHitStatement_of_qScheduleFirstHit hA hQ
  intro k hk4 rL rR hL hR hmax
  have haux7 : ∀ k : ℝ, 4 < k → Sec4.Aux7Statement.{0} k :=
    aux7_of_sixteen_div fun κ hκ hκ4 => Sec5.aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4
  exact HOuter.outerPocketCompletion_of_remaining h411 h51 (haux7 k hk4) hk4 hL hR hmax
    (OuterIn.r7OuterRemaining_of_inputs h411 h51 h47
      (fun θ h1 h2 => late_lemma47QHitTStatement hA h1 h2) hA _ hFH hlaws hk4 hL hR hmax
      (hgeom k hk4 rL rR hL hR hmax)
      (OuterIn.r7OuterSideRemaining_of_phase hk4 (hside k hk4 rL rR hL hR hmax)))

end InteractingSLE.Wire
