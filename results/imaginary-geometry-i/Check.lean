import InteractingSLE.Frozen.Spec.existsUnique_isBoundedHarmonicExtension_forceBoundaryData
import InteractingSLE.Frozen.Spec.exists_isOptionalHullCoupling
import InteractingSLE.Frozen.Spec.exists_measurable_lifetime_trace_eq_comp_field
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution_ae_exists_isGeneratingTrace
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_completedRange_eq_closure_lightCone
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_boundaryWalks_frontiers
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_componentKernels
import InteractingSLE.Frozen.Spec.IsFlowLine_stays_right_of_lt
import InteractingSLE.Frozen.Spec.IsFlowLine_merges
import InteractingSLE.Frozen.Spec.IsFlowLine_crosses_of_lt
import InteractingSLE.Frozen.Spec.exists_isIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution_measure_killedState_eq
import InteractingSLE.Frozen.Spec.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore
import InteractingSLE.Frozen.Spec.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData_existsUnique_isBoundedHarmonicExtension
import InteractingSLE.Frozen.Spec.exists_isFlowLine
import InteractingSLE.Frozen.Spec.exists_isStagedHistory
import Mathlib.Util.AssertNoSorry

/-! Release audit of the advertised theorems of *Imaginary geometry I* (Miller–Sheffield): the 17 frozen theorems
(Theorems 1.1–1.5, 2.2, 2.4, 2.6 and three companions). Every `#print axioms` report must list only axioms among
`propext`, `Classical.choice` and `Quot.sound` (any subset). -/
set_option autoImplicit false

-- Theorem 1.1, the force-point boundary data (companion).
assert_no_sorry InteractingSLE.existsUnique_isBoundedHarmonicExtension_forceBoundaryData
#print axioms InteractingSLE.existsUnique_isBoundedHarmonicExtension_forceBoundaryData
-- Theorem 1.1 (the optional hull coupling).
assert_no_sorry InteractingSLE.exists_isOptionalHullCoupling
#print axioms InteractingSLE.exists_isOptionalHullCoupling
-- Theorem 1.2 (the path is determined by the field).
assert_no_sorry InteractingSLE.exists_measurable_lifetime_trace_eq_comp_field
#print axioms InteractingSLE.exists_measurable_lifetime_trace_eq_comp_field
-- Theorem 1.3 (a continuous generating trace).
assert_no_sorry InteractingSLE.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace
#print axioms InteractingSLE.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace
-- Theorem 1.4, the light cone.
assert_no_sorry InteractingSLE.IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone
#print axioms InteractingSLE.IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone
-- Theorem 1.4, the boundary walks and frontiers.
assert_no_sorry InteractingSLE.IsCenteredCounterflowDriver.boundaryWalks_frontiers
#print axioms InteractingSLE.IsCenteredCounterflowDriver.boundaryWalks_frontiers
-- Theorem 1.4, the component kernels.
assert_no_sorry InteractingSLE.IsCenteredCounterflowDriver.componentKernels
#print axioms InteractingSLE.IsCenteredCounterflowDriver.componentKernels
-- Theorem 1.5 (i) (monotonicity).
assert_no_sorry InteractingSLE.IsFlowLine.stays_right_of_lt
#print axioms InteractingSLE.IsFlowLine.stays_right_of_lt
-- Theorem 1.5 (ii) (merging).
assert_no_sorry InteractingSLE.IsFlowLine.merges
#print axioms InteractingSLE.IsFlowLine.merges
-- Theorem 1.5 (iii) (crossing).
assert_no_sorry InteractingSLE.IsFlowLine.crosses_of_lt
#print axioms InteractingSLE.IsFlowLine.crosses_of_lt
-- Theorem 2.2, existence.
assert_no_sorry InteractingSLE.exists_isIntegratedSLEEvolution
#print axioms InteractingSLE.exists_isIntegratedSLEEvolution
-- Theorem 2.2, uniqueness in law.
assert_no_sorry InteractingSLE.IsIntegratedSLEEvolution.measure_killedState_eq
#print axioms InteractingSLE.IsIntegratedSLEEvolution.measure_killedState_eq
-- Theorem 2.4 (martingale characterization).
assert_no_sorry InteractingSLE.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore
#print axioms InteractingSLE.exists_isIntegratedSLEEvolution_iff_forall_isContLocalMartingaleBefore
-- Theorem 2.6 (conformal-radius martingales).
assert_no_sorry InteractingSLE.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius
#print axioms InteractingSLE.exists_isIntegratedSLEEvolution_eqOn_of_isContLocalMartingaleBefore_conformalRadius
-- Companion: piecewise-constant boundary data.
assert_no_sorry InteractingSLE.IsPiecewiseConstantBoundaryData.existsUnique_isBoundedHarmonicExtension
#print axioms InteractingSLE.IsPiecewiseConstantBoundaryData.existsUnique_isBoundedHarmonicExtension
-- Companion: existence of flow lines.
assert_no_sorry InteractingSLE.exists_isFlowLine
#print axioms InteractingSLE.exists_isFlowLine
-- Companion: existence of staged histories.
assert_no_sorry InteractingSLE.exists_isStagedHistory
#print axioms InteractingSLE.exists_isStagedHistory

/-! Every declaration of the included project modules (the `InteractingSLE`, `MathFin` and `BrownianMotion` modules
and the released `QuantumZipper`, `LQGMetric`, `LQGDimension`, `SupercriticalConformalCovariance`,
`SmallGammaGeodesics` and `GaussianLQG` modules they import) reaches only the three standard axioms. -/
open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let included : List Name := [`InteractingSLE, `MathFin, `BrownianMotion, `QuantumZipper, `LQGMetric, `LQGDimension,
    `SupercriticalConformalCovariance, `SmallGammaGeodesics, `GaussianLQG]
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := moduleNames[idx.toNat]!
    if included.any (·.isPrefixOf m) then
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
  logInfo m!"IMAGINARY_GEOMETRY_I_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
