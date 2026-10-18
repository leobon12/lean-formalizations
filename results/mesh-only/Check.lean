import MeshOnly.MeshOnlyConvergence
import MeshRates.Theorem11RateProof
import MeshRates.Corollary12.Full
import MeshRates.Section1Dirichlet
import MeshRates.PathToBoundary
import MeshRates.Section2Comparison
import MeshRates.Section4Clock
import MeshRates.Section4Crossing
import Mathlib.Util.AssertNoSorry

/-! Mesh-only convergence and sharper rates: exact statements, absence of `sorry` and axioms of
Theorem 1.1, Corollary 1.2 and every named lemma, then an axiom audit of every declaration in the
included `MeshRates`, `MeshOnly` and `BouRabeeGwynne` modules. The result guide documents the
correspondence with the paper. -/

/-! ## Earlier qualitative theorem (nine-page draft) -/
#check (BouRabeeGwynne.meshOnly_theorem11_proved : BouRabeeGwynne.MeshOnlyTheorem11Statement)
assert_no_sorry BouRabeeGwynne.meshOnly_theorem11_proved
#print axioms BouRabeeGwynne.meshOnly_theorem11_proved

open BouRabeeGwynne.MeshRates

/-! ## Headline results -/
#check (theorem11_full : MeshRatesTheorem11Statement)
#check (theorem11_qualitative : MeshRatesTheorem11QualitativeStatement)
#check (theorem11_rate : MeshRatesTheorem11RateStatement)
#check (corollary12_full : MeshRatesCorollary12Statement)
#check (corollary12_assumptionD : MeshRatesCorollary12AssumptionDStatement)
#check (corollary12_harmonicMeasure : MeshRatesCorollary12HarmonicMeasureStatement)
#check (corollary12_stoppedWalk : MeshRatesCorollary12StoppedWalkStatement)

assert_no_sorry theorem11_full
assert_no_sorry corollary12_full

#print axioms theorem11_full
#print axioms corollary12_full

/-! ## Named lemma-level results (MR §§1–6) -/
assert_no_sorry lemma8_dirichlet_maximum
assert_no_sorry mr_p3_pathToBoundary
assert_no_sorry wellPosed_of_mesh_le
assert_no_sorry lemma21_nu_le_tileL2_add_energy
assert_no_sorry lemma22_bvSobolev
assert_no_sorry prop23_defectiveNash_and_support
assert_no_sorry prop31_onDiagonal_and_survival
assert_no_sorry lemma41_localPowerPotential
assert_no_sorry lemma42_exactClock
assert_no_sorry prop43_ball_crossing_le
assert_no_sorry lemma51_energy_and_l2_error
assert_no_sorry lemma61_expectedExitTime_le
assert_no_sorry section6_oneSided_estimate

#print axioms lemma8_dirichlet_maximum
#print axioms mr_p3_pathToBoundary
#print axioms wellPosed_of_mesh_le
#print axioms lemma21_nu_le_tileL2_add_energy
#print axioms lemma22_bvSobolev
#print axioms prop23_defectiveNash_and_support
#print axioms prop31_onDiagonal_and_survival
#print axioms lemma41_localPowerPotential
#print axioms lemma42_exactClock
#print axioms prop43_ball_crossing_le
#print axioms lemma51_energy_and_l2_error
#print axioms lemma61_expectedExitTime_le
#print axioms section6_oneSided_estimate

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
    if (`MeshRates).isPrefixOf m || (`MeshOnly).isPrefixOf m || (`BouRabeeGwynne).isPrefixOf m then
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
  logInfo m!"MESH_RATES_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
