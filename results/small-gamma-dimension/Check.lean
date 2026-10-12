import LQGDimension.Assembly.Theorem11
import LQGDimension.Existence.Assembly
import LQGDimension.Sanity
import Mathlib.Util.AssertNoSorry

/-! Named proofs for Theorem 1.1 and GFF non-vacuity. The result guide documents the explicit
LFPP exponent and LQG dimension hypotheses inherited from the manuscript. -/
#check (LQGDimension.theorem11 : LQGDimension.Theorem11)
#check (LQGDimension.theorem11_aStar : LQGDimension.Theorem11_AStar)
#check (LQGDimension.theorem11_lambda : LQGDimension.Theorem11_Lambda)
#check (LQGDimension.theorem11_dimension : LQGDimension.Theorem11_Dimension)
#check (LQGDimension.prop12Upper : LQGDimension.Blueprint.Prop12Upper)
#check (LQGDimension.prop12Lower : LQGDimension.Blueprint.Prop12Lower)
#check (LQGDimension.gffCircleAverageExists :
  LQGDimension.Blueprint.Existence.GFFCircleAverageExists)
assert_no_sorry LQGDimension.theorem11
assert_no_sorry LQGDimension.gffCircleAverageExists
#print axioms LQGDimension.theorem11
#print axioms LQGDimension.gffCircleAverageExists

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
    if (`LQGDimension).isPrefixOf m then
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
  logInfo m!"SMALL_GAMMA_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
