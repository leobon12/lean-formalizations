/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12RelayChart
import InteractingSLE.Spec.Sec5.CfPhysUpper
import InteractingSLE.Spec.Wire.Thm12LateA2
import InteractingSLE.Spec.Wire.PartAClearanceRegularity
import InteractingSLE.Spec.ZhanGT4.A1G3RRMain
import InteractingSLE.Spec.ZhanGT4.A1G3L2SndStopMain
import InteractingSLE.Spec.ZhanGT4.A1G3LgFinal
import InteractingSLE.Spec.ZhanGT4.A1ESRecWire

/-!
# Theorem 1.2's raw chart members, with no input

Packet PROVE-CHART-RAW. `Wire.Relay.RawChartMembersOn` is CFCARRY's raw physical locality premise.

* `rawChartMembersOn_of_reference`: it follows from the §4.2 reference coupling by PROVE-CFCHART2's
  `CfPhys.hasSafeMembers_imgField_coarse` (raw physical locality on the original space; the (4.4) height bounds
  give Cond44 and the θ bounds).
* `partAInputs`, `cond44ReferenceStatement`: clearance Part A and the reference coupling hold outright, because
  all four C-form directions of Zhan's A.1 are proved (G3: `A1G3L2.g3RectLawSndC_holds`,
  `A1G3Lg.g3RectLawFstC_holds` with the rows `A1G3RR.g3RectRow`; Eight: `A1ESRec.a1DualCouplingEightCoreStatement`).
  The route is the one of Theorem 1.2's assembly (`T12Asm.theorem12Statement_assembled`): Part A, Lemma 4.7Q,
  Proposition 4.11Q, the reference coupling.
* `rawChartMembersOn`: the raw members at every universe, with no hypothesis.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Sec5.ChartRaw

/-- **Raw chart members from the reference coupling** (PROVE-CFCHART2's original-space raw locality). -/
theorem rawChartMembersOn_of_reference (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u}) :
    Wire.Relay.RawChartMembersOn.{u} := by
  intro κ θ b J Ω mΩ hSB P hP h W' ζ' hκ hκ4 hb _hh hcf _hζ' hθh hπh _hθ D _hDm hDreg _hD s _hs η _hη
  dsimp only
  intro h' 𝓕 VL VR B N E _hι htr hC hN hm hE hEg _hTop hEae
  exact CfPhys.hasSafeMembers_imgField_coarse href hκ hκ4 (Theorem15.isOrderedForceWord_flowLine b J 0)
    (Sec7.R7Outer.cond44_of_heights hκ hb hθh)
    (RestartGen.cfThetaBounds_of_heights hκ hκ4 hb hπh θ) hC htr hcf hDreg hN hm hE hEg hEae

/-- Zhan's A.1 Core statement (G3) for every parameter: the rows and both proved C-form directions. -/
theorem g3CoreStatement (κ : ℝ) : ZhanGT4.A1Canon.A1DualCouplingG3CoreStatement κ :=
  ZhanGT4.A1RLaw.a1DualCouplingG3CoreStatement_of_dirsC (ZhanGT4.A1G3RR.g3RectRow κ)
    (ZhanGT4.A1G3L2.g3RectLawSndC_holds κ) (ZhanGT4.A1G3Lg.g3RectLawFstC_holds κ)

/-- **Clearance Part A holds**: both A.1 Core statements are proved. -/
theorem partAInputs : PartAInputsSixteenDivOfClearance :=
  Wire.late_partAInputs g3CoreStatement ZhanGT4.A1ESRec.a1DualCouplingEightCoreStatement

/-- **The §4.2 reference coupling holds**: Part A, Lemma 4.7Q, Proposition 4.11Q. -/
theorem cond44ReferenceStatement : Sec7.Lemma71H.Cond44ReferenceStatement.{u} :=
  Cond44Ref.cond44ReferenceStatement_of_prop411Q
    (Prop49Exit.prop411QStatement_of_lemma47Q_of_partA_of_clearance
      (Wire.late_lemma47QHitStatement partAInputs) partAInputs)

/-- **Theorem 1.2's `hChartRaw` holds**: the restart chart's raw member identities, at every universe. -/
theorem rawChartMembersOn : Wire.Relay.RawChartMembersOn.{u} :=
  rawChartMembersOn_of_reference cond44ReferenceStatement

end InteractingSLE.Sec5.ChartRaw
