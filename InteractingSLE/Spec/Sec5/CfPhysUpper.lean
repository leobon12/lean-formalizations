/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysSource

/-!
# The upper (4.4) counterflow chart with raw physical locality discharged

Packet PROVE-CFCHART2. The landed joint base/reduction construction, zero-prefix
case and integrability are reused. Raw physical locality is supplied by the
physical marked union and the proved strict inverse-capacity passage.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfPhys

/-- The exact upper (4.4) chart, with no raw-member or chart-locality input. -/
theorem cfGivenChart44UpStatement (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : QSched.CfGivenChart44UpStatement.{u} := by
  refine CfCarry.cfGivenChart44Up_of_raw_members hA href ?_
  intro κ θ b J Ω mΩ hSB P hP h W' ζ' hκ hκ4 hb _hh hcf _hζ' hθh hπh _hθ D _hDm hDreg _hD s
    _hs η _hη
  dsimp only
  intro h' 𝓕 VL VR B N E _hι htr hC hN hm hE hEg _hTop hEae
  exact hasSafeMembers_imgField_coarse href hκ hκ4 (Theorem15.isOrderedForceWord_flowLine b J 0)
    (Sec7.R7Outer.cond44_of_heights hκ hb hθh)
    (RestartGen.cfThetaBounds_of_heights hκ hκ4 hb hπh θ) hC htr hcf hDreg hN hm hE hEg hEae

/-- The original uniform-height chart follows from the proved upper (4.4) chart. -/
theorem cfGivenChartStatement (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) : CfGiven.CfGivenChartStatement.{u} :=
  CfCarry.cfGivenChartStatement_of_up44 (cfGivenChart44UpStatement hA href)

/-- The schedule first-hit input, with only its separate mirror-height chart
branch left beyond the existing schedule inputs. -/
theorem qScheduleFirstHitStatement_of_down44
    (hA : PartAInputsSixteenDivOfClearance)
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (h47 : Prop411Q.Lemma47QHitStatement.{u}) (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hDn : QSched.CfGivenChart44DownStatement.{u}) : FrameQ.QScheduleFirstHitStatement.{u} :=
  CfCarry.qScheduleFirstHitStatement_of_up44 h44 h47 href (cfGivenChart44UpStatement hA href) hDn

end InteractingSLE.Sec5.CfPhys
