import BouRabeeGwynne.TheoremAProved
import BouRabeeGwynne.Section3TheoremBPartA
import ReflectedWalk.Theorem16Closed
import ReflectedGMS.GMS.Theorem116
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

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if (`BouRabeeGwynne).isPrefixOf m || (`ReflectedWalk).isPrefixOf m ||
        (`ReflectedGMS).isPrefixOf m then
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
