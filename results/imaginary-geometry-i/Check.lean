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
import InteractingSLE.Frozen.Spec.IsFlowLine_merges_of_contact
import InteractingSLE.Frozen.Spec.IsFlowLine_crosses_of_lt_of_contact
import InteractingSLE.Frozen.Spec.exists_strongMarkovKernel_isIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_boundaryWalks_outerBoundaries
import InteractingSLE.Spec.AuditFix.LiteralCounterflow
import InteractingSLE.Spec.AuditFix.FrontierBridge
import InteractingSLE.Spec.AuditFix.Markov
import InteractingSLE.Spec.AuditFix.BoundaryContact
import InteractingSLE.Spec.AuditFix.BoundaryContactStrong
import InteractingSLE.Spec.AuditFix.StrongCross
import InteractingSLE.Frozen.Spec.IsFlowLine_start_or_terminal_of_contact_of_critical
import InteractingSLE.Frozen.Spec.IsFlowLine_first_or_terminal_of_contact_of_critical
import InteractingSLE.Spec.RealContact.Main
import InteractingSLE.Frozen.Spec.IsCenteredCounterflowDriver_completedRange_eq_closure_lightCone_of_schedule
import InteractingSLE.Spec.LightConeAllQ.Main
import Mathlib.Util.AssertNoSorry

/-! Release audit of the advertised theorems of *Imaginary geometry I* (Miller–Sheffield): the 21 frozen theorems
(Theorems 1.1–1.5, 2.2, 2.4, 2.6, four companions, and four statements added after the external audit of
2026-11-15), the two critical-angle statements of Theorem 1.5 at every contact and Theorem 1.4's light cone for every
prescribed schedule set (2026-11-16), then the supplementary theorems of the audit response, of the critical-angle proof
and of the light-cone proof. Every `#print axioms` report must list only axioms among
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

-- Added after the external audit of 2026-11-15 (ruling R122): frozen and sealed.
-- Theorem 1.5 (ii) at every contact.
assert_no_sorry InteractingSLE.IsFlowLine.merges_of_contact
#print axioms InteractingSLE.IsFlowLine.merges_of_contact
-- Theorem 1.5 (iii) at every available contact, with no common outgoing arc.
assert_no_sorry InteractingSLE.IsFlowLine.crosses_of_lt_of_contact
#print axioms InteractingSLE.IsFlowLine.crosses_of_lt_of_contact
-- Theorem 2.2, the Markov sentence (strong Markov property).
assert_no_sorry InteractingSLE.exists_strongMarkovKernel_isIntegratedSLEEvolution
#print axioms InteractingSLE.exists_strongMarkovKernel_isIntegratedSLEEvolution
-- Theorem 1.4, the walks are the left and right boundaries (nowhere boundary filling).
assert_no_sorry InteractingSLE.IsCenteredCounterflowDriver.boundaryWalks_outerBoundaries
#print axioms InteractingSLE.IsCenteredCounterflowDriver.boundaryWalks_outerBoundaries

-- Added 2026-11-16 (rulings R124, R125): frozen and sealed.
-- Theorem 1.5 (i), critical angles, at every contact (real points and terminal values included).
assert_no_sorry InteractingSLE.IsFlowLine.start_or_terminal_of_contact_of_critical
#print axioms InteractingSLE.IsFlowLine.start_or_terminal_of_contact_of_critical
-- Theorem 1.5 (iii), critical angles, at every contact (real points and terminal values included).
assert_no_sorry InteractingSLE.IsFlowLine.first_or_terminal_of_contact_of_critical
#print axioms InteractingSLE.IsFlowLine.first_or_terminal_of_contact_of_critical
-- Theorem 1.4, light cone, for every prescribed schedule set (rulings R126, R127), e.g. the positive rationals.
assert_no_sorry InteractingSLE.IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone_of_schedule
#print axioms InteractingSLE.IsCenteredCounterflowDriver.completedRange_eq_closure_lightCone_of_schedule

-- Supplementary theorems of the audit response (statement-audited, not frozen).
assert_no_sorry InteractingSLE.AuditFix.literalCounterflowBridge_holds
#print axioms InteractingSLE.AuditFix.literalCounterflowBridge_holds
assert_no_sorry InteractingSLE.AuditFix.literalCounterflowWord_holds
#print axioms InteractingSLE.AuditFix.literalCounterflowWord_holds
assert_no_sorry InteractingSLE.AuditFix.literalCounterflowParamField_holds
#print axioms InteractingSLE.AuditFix.literalCounterflowParamField_holds
assert_no_sorry InteractingSLE.AuditFix.literalCounterflowBranch_holds
#print axioms InteractingSLE.AuditFix.literalCounterflowBranch_holds
assert_no_sorry InteractingSLE.AuditFix.shiftedField_holds
#print axioms InteractingSLE.AuditFix.shiftedField_holds
assert_no_sorry InteractingSLE.AuditFix.flowLineAngleShift_holds
#print axioms InteractingSLE.AuditFix.flowLineAngleShift_holds
assert_no_sorry InteractingSLE.AuditFix.literalCounterflowLightCone_holds
#print axioms InteractingSLE.AuditFix.literalCounterflowLightCone_holds
assert_no_sorry InteractingSLE.AuditFix.literalCounterflowFrontiers_holds
#print axioms InteractingSLE.AuditFix.literalCounterflowFrontiers_holds
assert_no_sorry InteractingSLE.AuditFix.literalCounterflowComponentKernels_holds
#print axioms InteractingSLE.AuditFix.literalCounterflowComponentKernels_holds
assert_no_sorry InteractingSLE.AuditFix.frontierBridge_holds
#print axioms InteractingSLE.AuditFix.frontierBridge_holds
assert_no_sorry InteractingSLE.AuditFix.frontierNowhereFilling_holds
#print axioms InteractingSLE.AuditFix.frontierNowhereFilling_holds
assert_no_sorry InteractingSLE.AuditFix.integratedSLEStrongMarkov_holds
#print axioms InteractingSLE.AuditFix.integratedSLEStrongMarkov_holds
assert_no_sorry InteractingSLE.AuditFix.integratedSLEMarkov_holds
#print axioms InteractingSLE.AuditFix.integratedSLEMarkov_holds
assert_no_sorry InteractingSLE.AuditFix.integratedSLEIncrementStrongMarkov_holds
#print axioms InteractingSLE.AuditFix.integratedSLEIncrementStrongMarkov_holds
assert_no_sorry InteractingSLE.AuditFix.mergesUponContact_holds
#print axioms InteractingSLE.AuditFix.mergesUponContact_holds
assert_no_sorry InteractingSLE.AuditFix.crossesUponContact_holds
#print axioms InteractingSLE.AuditFix.crossesUponContact_holds
assert_no_sorry InteractingSLE.AuditFix.crossesUponAvailableContact_holds
#print axioms InteractingSLE.AuditFix.crossesUponAvailableContact_holds
assert_no_sorry InteractingSLE.AuditFix.strongCrossesUponAvailableContact_holds
#print axioms InteractingSLE.AuditFix.strongCrossesUponAvailableContact_holds
assert_no_sorry InteractingSLE.AuditFix.criticalOrderedNoInteriorPoint_holds
#print axioms InteractingSLE.AuditFix.criticalOrderedNoInteriorPoint_holds
assert_no_sorry InteractingSLE.AuditFix.criticalCrossingNoLaterInteriorPoint_holds
#print axioms InteractingSLE.AuditFix.criticalCrossingNoLaterInteriorPoint_holds
assert_no_sorry InteractingSLE.AuditFix.strongCrossStatement_holds
#print axioms InteractingSLE.AuditFix.strongCrossStatement_holds

-- Supplementary theorems of the critical-angle proof (rulings R124, R125; not frozen): the two clauses in their
-- statement-audited form, the first-hit exclusion at real hits, the pocket corner, and the conditional law given the
-- completed second path.
assert_no_sorry InteractingSLE.RealContact.criticalOrderedContact_holds
#print axioms InteractingSLE.RealContact.criticalOrderedContact_holds
assert_no_sorry InteractingSLE.RealContact.criticalCrossingContact_holds
#print axioms InteractingSLE.RealContact.criticalCrossingContact_holds
assert_no_sorry InteractingSLE.RealContact.g7GB7aFirstHitReal_holds
#print axioms InteractingSLE.RealContact.g7GB7aFirstHitReal_holds
assert_no_sorry InteractingSLE.RealContact.pocketCorner_holds
#print axioms InteractingSLE.RealContact.pocketCorner_holds
assert_no_sorry InteractingSLE.RealContact.terminalRetainedCondDet_holds
#print axioms InteractingSLE.RealContact.terminalRetainedCondDet_holds
assert_no_sorry InteractingSLE.RealContact.terminalRetainedPath_holds
#print axioms InteractingSLE.RealContact.terminalRetainedPath_holds

-- Supplementary theorems of the light-cone proof (rulings R126, R127; not frozen): the statement-audited form, and
-- interior switching tips at every deterministic schedule.
assert_no_sorry InteractingSLE.LightConeAllQ.lightConeAllSchedule_holds
#print axioms InteractingSLE.LightConeAllQ.lightConeAllSchedule_holds
assert_no_sorry InteractingSLE.LightConeAllQ.gw2InteriorScheduleAllQ_holds
#print axioms InteractingSLE.LightConeAllQ.gw2InteriorScheduleAllQ_holds

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
