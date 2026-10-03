import BouRabeeGwynne.TheoremAProved
import BouRabeeGwynne.Section3TheoremBPartA
import ReflectedWalk.Theorem16Closed
import ReflectedGMS.GMS.Theorem116
import QuantumZipper.Proofs.Thm11.Final
import QuantumZipper.Proofs.Thm12.Main
import QuantumZipper.Proofs.Zipper.FieldLawler4Final
import QuantumZipper.Proofs.MainResults13
import QuantumZipper.Proofs.Section5.Prop1617Proved
import QuantumZipper.Proofs.MainResults18
import QuantumZipper.Proofs.Zipper.Cor15FullMain
import QuantumZipper.Proofs.Section5.Prop16GenMain
import QuantumZipper.Proofs.Section5.Prop16LitDilQ
import QuantumZipper.Proofs.Final13NonVacuity
import QuantumZipper.Proofs.Final18NonVacuity
import QuantumZipper.Proofs.NonVacuityAddendum
import QuantumZipper.Proofs.NonVacuityFinal
import QuantumZipper.Proofs.Section5.Prop16LitCert
import LQGMetric.Assembly.MainFinal
import Mathlib.Util.AssertNoSorry

/-! Verification of the selected public results and every declaration in their included modules.
The source-to-paper scope is documented in the result READMEs; compilation alone does not
establish correspondence between a Lean definition and a mathematical description. -/
set_option autoImplicit false
set_option pp.explicit true
set_option pp.universes true

#check @BouRabeeGwynne.theoremA_proved
#check @BouRabeeGwynne.theoremB_part_a
#check @ReflectedWalk.theorem16_closed
#check @ReflectedGMS.GMS.theorem1_16

example : BouRabeeGwynne.TheoremAStatement := BouRabeeGwynne.theoremA_proved
example : BouRabeeGwynne.TheoremBPartAStatement := BouRabeeGwynne.theoremB_part_a
example {V : Type*} (G : ReflectedWalk.ConductanceGraph V)
    (hmin : G.EnergyMinimizer) : ReflectedWalk.Theorem16Statement G hmin :=
  ReflectedWalk.theorem16_closed G hmin
example : ReflectedGMS.GMS.Theorem1_16 := ReflectedGMS.GMS.theorem1_16

assert_no_sorry BouRabeeGwynne.theoremA_proved
assert_no_sorry BouRabeeGwynne.theoremB_part_a
assert_no_sorry ReflectedWalk.theorem16_closed
assert_no_sorry ReflectedGMS.GMS.theorem1_16
#print axioms BouRabeeGwynne.theoremA_proved
#print axioms BouRabeeGwynne.theoremB_part_a
#print axioms ReflectedWalk.theorem16_closed
#print axioms ReflectedGMS.GMS.theorem1_16

/-! ## The eight Section 1 results -/

#check (QuantumZipper.Thm11Asm.theorem1_1_proved : QuantumZipper.theorem1_1)
assert_no_sorry QuantumZipper.Thm11Asm.theorem1_1_proved
#print axioms QuantumZipper.Thm11Asm.theorem1_1_proved

#check (QuantumZipper.theorem1_2_holds : QuantumZipper.theorem1_2)
assert_no_sorry QuantumZipper.theorem1_2_holds
#print axioms QuantumZipper.theorem1_2_holds

#check (QuantumZipper.theorem1_3_proved : QuantumZipper.theorem1_3)
assert_no_sorry QuantumZipper.theorem1_3_proved
#print axioms QuantumZipper.theorem1_3_proved

#check (QuantumZipper.theorem1_4_proved : QuantumZipper.theorem1_4)
assert_no_sorry QuantumZipper.theorem1_4_proved
#print axioms QuantumZipper.theorem1_4_proved

#check (QuantumZipper.theorem1_5_proved : QuantumZipper.theorem1_5)
assert_no_sorry QuantumZipper.theorem1_5_proved
#print axioms QuantumZipper.theorem1_5_proved

#check (QuantumZipper.theorem1_6_proved : QuantumZipper.theorem1_6)
assert_no_sorry QuantumZipper.theorem1_6_proved
#print axioms QuantumZipper.theorem1_6_proved

#check (QuantumZipper.theorem1_7_proved : QuantumZipper.theorem1_7)
assert_no_sorry QuantumZipper.theorem1_7_proved
#print axioms QuantumZipper.theorem1_7_proved

#check (QuantumZipper.theorem1_8_proved : QuantumZipper.Paper18.theorem1_8PaperMO)
assert_no_sorry QuantumZipper.theorem1_8_proved
#print axioms QuantumZipper.theorem1_8_proved

/-! ## Companions closer to the paper's wording -/

#check (QuantumZipper.theorem1_5_full_proved : QuantumZipper.theorem1_5_full)
assert_no_sorry QuantumZipper.theorem1_5_full_proved
#print axioms QuantumZipper.theorem1_5_full_proved

#check (QuantumZipper.theorem1_6_general_proved : QuantumZipper.theorem1_6_general)
assert_no_sorry QuantumZipper.theorem1_6_general_proved
#print axioms QuantumZipper.theorem1_6_general_proved

#check (QuantumZipper.Prop16Lit.theorem1_6_literal_proved : QuantumZipper.theorem1_6_literal)
assert_no_sorry QuantumZipper.Prop16Lit.theorem1_6_literal_proved
#print axioms QuantumZipper.Prop16Lit.theorem1_6_literal_proved

/-! ## Non-vacuity certificates -/

#check @QuantumZipper.Final13.thm13_certificate
assert_no_sorry QuantumZipper.Final13.thm13_certificate
#print axioms QuantumZipper.Final13.thm13_certificate
#check @QuantumZipper.Final18.thm18_hypotheses_satisfiable
assert_no_sorry QuantumZipper.Final18.thm18_hypotheses_satisfiable
#print axioms QuantumZipper.Final18.thm18_hypotheses_satisfiable
#check @QuantumZipper.NonVacuityAddendum.addendum_hypotheses_nonvacuous
assert_no_sorry QuantumZipper.NonVacuityAddendum.addendum_hypotheses_nonvacuous
#print axioms QuantumZipper.NonVacuityAddendum.addendum_hypotheses_nonvacuous
#check @QuantumZipper.NonVacuity.exists_BM_indep_freeGFF_uncond
assert_no_sorry QuantumZipper.NonVacuity.exists_BM_indep_freeGFF_uncond
#print axioms QuantumZipper.NonVacuity.exists_BM_indep_freeGFF_uncond
#check @QuantumZipper.NonVacuity.exists_BM_indep_zeroGFF_uncond
assert_no_sorry QuantumZipper.NonVacuity.exists_BM_indep_zeroGFF_uncond
#print axioms QuantumZipper.NonVacuity.exists_BM_indep_zeroGFF_uncond
#check @QuantumZipper.Prop16LitCert.exists_litChart_family_halfDisc
assert_no_sorry QuantumZipper.Prop16LitCert.exists_litChart_family_halfDisc
#print axioms QuantumZipper.Prop16LitCert.exists_litChart_family_halfDisc

#check @QuantumZipper.NonVacuityAddendum.exists_addendum_setup
assert_no_sorry QuantumZipper.NonVacuityAddendum.exists_addendum_setup
#print axioms QuantumZipper.NonVacuityAddendum.exists_addendum_setup

/-! ## The statements -/

#print QuantumZipper.theorem1_1
#print QuantumZipper.theorem1_2
#print QuantumZipper.theorem1_3
#print QuantumZipper.theorem1_4
#print QuantumZipper.theorem1_5
#print QuantumZipper.theorem1_6
#print QuantumZipper.theorem1_7
#print QuantumZipper.Paper18.theorem1_8PaperMO

#print QuantumZipper.theorem1_5_full
#print QuantumZipper.theorem1_6_general
#print QuantumZipper.theorem1_6_literal

/-! ## Gwynne–Miller: existence and uniqueness of the LQG metric -/

#check (LQGMetric.theorem11_proved : LQGMetric.Theorem11)
assert_no_sorry LQGMetric.theorem11_proved
#print axioms LQGMetric.theorem11_proved

#check (LQGMetric.theorem12_proved : LQGMetric.Theorem12)
assert_no_sorry LQGMetric.theorem12_proved
#print axioms LQGMetric.theorem12_proved

#check LQGMetric.main_result
assert_no_sorry LQGMetric.main_result
#print axioms LQGMetric.main_result

#check LQGMetric.theorem11_proved_measurable
assert_no_sorry LQGMetric.theorem11_proved_measurable
#print axioms LQGMetric.theorem11_proved_measurable

#check LQGMetric.theorem12_existence_measurable
assert_no_sorry LQGMetric.theorem12_existence_measurable
#print axioms LQGMetric.theorem12_existence_measurable

#print LQGMetric.Theorem11
#print LQGMetric.Theorem12

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := moduleNames[idx.toNat]!
    if (`BouRabeeGwynne).isPrefixOf m || (`ReflectedWalk).isPrefixOf m ||
        (`ReflectedGMS).isPrefixOf m || (`QuantumZipper).isPrefixOf m ||
        (`LQGDimension).isPrefixOf m || (`LQGMetric).isPrefixOf m then
      roots := roots.push n
  if roots.isEmpty then throwError "No included declarations found"
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "Missing declaration {n}"
    match ci with
    | .axiomInfo _ =>
      axioms := axioms.insert n
      unless allowed.contains n do
        throwError "Disallowed axiom reachable from included declarations: {n}"
    | _ => pure ()
    pending := pending ++ ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then
      pending := pending ++ v.getUsedConstants
  logInfo m!"PUBLIC_RELEASE_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
