import LQGDimension.Assembly.Theorem11
import LQGDimension.Existence.Assembly
import LQGDimension.Sanity
import MeshOnly.MeshOnlyConvergence
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
import MeshRates.Theorem11RateProof
import MeshRates.Corollary12.Full
import MeshRates.Section1Dirichlet
import MeshRates.PathToBoundary
import MeshRates.Section2Comparison
import MeshRates.Section4Clock
import MeshRates.Section4Crossing
import GaussianLQG.Frozen.MainTheorem
import HigherDimLFPP.Frozen.MainTheorem
import HigherDimLFPP.Frozen.DimensionComparison
import HigherDimLFPP.Frozen.KappaTwo
import HigherDimLFPP.Frozen.BandVecNormSq
import HigherDimLFPP.Frozen.FieldExists
import HigherDimLFPP.Frozen.LQGDimensionAsymptotics
import HigherDimLFPP.Frozen.GFFCircleAverage
import SmallGammaGeodesics.Frozen.DeviationScale
import SmallGammaGeodesics.Frozen.FunctionalTightness
import SmallGammaGeodesics.Frozen.GeodesicAeUnique
import HigherDimLQGMetric.Frozen.Theorem12
import HigherDimLQGMetric.Frozen.Theorem14
import HigherDimLQGMetric.Frozen.Theorem14Sharp
import HigherDimLQGMetric.Frozen.StrongUniqueness
import HigherDimLQGMetric.Frozen.SharpWeakNonempty
import HigherDimLQGMetric.Frozen.DistExpSpec
import HigherDimLQGMetric.Frozen.SubcriticalNonempty
import HigherDimLQGMetric.Frozen.NormLGFLawSpec
import HigherDimLQGMetric.Frozen.ConvKernelSmoothIntegral
import HigherDimLQGMetric.Frozen.SphereAvgSpec
import HigherDimLQGMetric.Frozen.ConvMollifySpec
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
    if (`MeshOnly).isPrefixOf m || (`BouRabeeGwynne).isPrefixOf m || (`ReflectedWalk).isPrefixOf m ||
        (`ReflectedGMS).isPrefixOf m || (`QuantumZipper).isPrefixOf m ||
        (`LQGDimension).isPrefixOf m || (`LQGMetric).isPrefixOf m || (`MeshRates).isPrefixOf m ||
        (`GaussianLQG).isPrefixOf m || (`HigherDimLFPP).isPrefixOf m ||
        (`SmallGammaGeodesics).isPrefixOf m ||
        (`HigherDimLQGMetric).isPrefixOf m then
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

#check (BouRabeeGwynne.meshOnly_theorem11_proved : BouRabeeGwynne.MeshOnlyTheorem11Statement)
assert_no_sorry BouRabeeGwynne.meshOnly_theorem11_proved
#print axioms BouRabeeGwynne.meshOnly_theorem11_proved
#check (BouRabeeGwynne.MeshRates.theorem11_full : BouRabeeGwynne.MeshRates.MeshRatesTheorem11Statement)
#check (BouRabeeGwynne.MeshRates.corollary12_full : BouRabeeGwynne.MeshRates.MeshRatesCorollary12Statement)
assert_no_sorry BouRabeeGwynne.MeshRates.theorem11_full
assert_no_sorry BouRabeeGwynne.MeshRates.corollary12_full
#print axioms BouRabeeGwynne.MeshRates.theorem11_full
#print axioms BouRabeeGwynne.MeshRates.corollary12_full
assert_no_sorry ReflectedGMS.GeomTop.geomHarmonicCoordinateMainTheorem
assert_no_sorry ReflectedGMS.GeomTop.geomReflectedInvarianceMainTheorem
#print axioms ReflectedGMS.GeomTop.geomHarmonicCoordinateMainTheorem
#print axioms ReflectedGMS.GeomTop.geomReflectedInvarianceMainTheorem


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


/-! ## First-order fluctuations of small-γ LQG distance

The frozen main theorem `GaussianLQG.main_theorem` (Theorem 1.1 of the source note). The `example`
restates its type verbatim from `GaussianLQG/Frozen/MainTheorem.lean`; the result guide documents the
correspondence with the paper. -/

section GaussianLQGRelease
open MeasureTheory ProbabilityTheory Filter Topology Set

set_option pp.explicit false in
set_option pp.universes false in
#check GaussianLQG.main_theorem

namespace GaussianLQG

example :
    ∀ (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (_hh : LQGMetric.IsNormalizedWPGFF h P),
    -- `q` is the unique median of `M`, and `q < 0`
    (LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) qConst ∧
      ∀ m, LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) m → m = qConst) ∧
    qConst < 0 ∧
    -- (1.7): convergence in probability
    TendstoInMeasure P (fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) ∧
    -- the limit has law `N(-q/2, 3/8)`
    P.map (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) =
      gaussianReal (-qConst / 2) (3 / 8 : NNReal) ∧
    -- (1.8): convergence in law to `N(-q/2, 3/8)` (indexed by `γ ∈ (0,2)`)
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) ω => ((D γ (h ω)).1 (0, 1) - 1) / (γ : ℝ))
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal (-qConst / 2) (3 / 8 : NNReal)) ∧
    -- (1.9) for every choice of medians `m_γ` of `D^γ(0,1)`
    ∀ m : ℝ → ℝ, (∀ γ, 0 < γ → γ < 2 →
        LQGMetric.IsMedian (P.map fun ω => (D γ (h ω)).1 (0, 1)) (m γ)) →
      Tendsto (fun γ => (m γ - (1 - qConst / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0) :=
  main_theorem

end GaussianLQG
end GaussianLQGRelease

assert_no_sorry GaussianLQG.main_theorem
#print axioms GaussianLQG.main_theorem

/-! ## A small-parameter limit for higher-dimensional LFPP

The frozen main theorem `HigherDimLFPP.theorem11` (Theorem 1.1 of the source paper, in every dimension
`d ≥ 2`) and the six further frozen theorems of that release. The `example`s restate their types
verbatim from `HigherDimLFPP/Frozen/`; the result guide documents the correspondence with the paper. -/

section HigherDimLFPPRelease
open MeasureTheory ProbabilityTheory Filter Topology Set

set_option pp.explicit false in
set_option pp.universes false in
#check HigherDimLFPP.theorem11

namespace HigherDimLFPP

example : ∀ d : ℕ, 2 ≤ d →
    (∀ n : ℕ, A n d ≠ ⊥ ∧ A n d ≠ ⊤) ∧
    (∀ n r : ℕ, A (n + r) d ≤ A n d + A r d) ∧
    Tendsto (fun n : ℕ => (A n d).toReal / ((n : ℝ) * Real.log 2)) atTop (𝓝 (kappa d)) ∧
    0 < kappa d ∧
    ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ), IsWhiteNoise P W →
    ∀ H : ℝ → Rd d → Ω → ℝ, (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, ∃ lam : ℝ, IsLFPPExponent H P ζ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ζ₀ > 0, ∀ ζ ∈ Ioo (0 : ℝ) ζ₀, IsLFPPExponent H P ζ (lam ζ)) →
        Tendsto (fun ζ => lam ζ / ζ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa d)) :=
  theorem11

example : ∀ d : ℕ, 2 ≤ d →
    ((d : ℝ) - 1) ^ (2 / 3 : ℝ) * kappa 2 ≤ kappa d ∧ kappa d ≤ ((d : ℝ) - 1) * kappa 2 :=
  dimension_comparison

example : kappa 2 = LQGDimension.aStar / Real.log 16 :=
  kappa_two_eq

example : ∀ d : ℕ, 1 ≤ d → ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
    ∀ a b : ℝ, 0 < a → a < b → ∀ z : Rd d,
      MemLp (bandKernel κ a b z) 2 volume ∧ ‖bandVec κ a b z‖ ^ 2 = Real.log (b / a) :=
  bandVec_norm_sq

example : ∀ d : ℕ, 1 ≤ d →
    (∃ κ : Rd d → ℝ, IsLFPPKernel κ) ∧
    ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℝ → Rd d → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsWhiteNoise P W ∧
          ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε) :=
  field_exists

example : Tendsto (fun γ : ℝ => (LQGMetric.dGamma γ - 2) / γ ^ (4 / 3 : ℝ)) (𝓝[>] 0)
      (𝓝 (2 ^ (-1 / 3 : ℝ) * kappa 2)) :=
  lqg_dimension_asymptotics

example : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
      LQGDimension.IsGFFCircleAverage h P →
      (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, ∃ lam : ℝ, LQGDimension.IsLFPPExponent h P ξ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, LQGDimension.IsLFPPExponent h P ξ (lam ξ)) →
        Tendsto (fun ξ => lam ξ / ξ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa 2)) :=
  gff_circle_average_lfpp

end HigherDimLFPP
end HigherDimLFPPRelease

assert_no_sorry HigherDimLFPP.theorem11
assert_no_sorry HigherDimLFPP.dimension_comparison
assert_no_sorry HigherDimLFPP.kappa_two_eq
assert_no_sorry HigherDimLFPP.bandVec_norm_sq
assert_no_sorry HigherDimLFPP.field_exists
assert_no_sorry HigherDimLFPP.lqg_dimension_asymptotics
assert_no_sorry HigherDimLFPP.gff_circle_average_lfpp
#print axioms HigherDimLFPP.theorem11
#print axioms HigherDimLFPP.dimension_comparison
#print axioms HigherDimLFPP.kappa_two_eq
#print axioms HigherDimLFPP.bandVec_norm_sq
#print axioms HigherDimLFPP.field_exists
#print axioms HigherDimLFPP.lqg_dimension_asymptotics
#print axioms HigherDimLFPP.gff_circle_average_lfpp

/-! ## Small-parameter LQG geodesics: deviation and functional tightness

The frozen theorems `SmallGammaGeodesics.deviation_scale` (Theorem 1.1 of the source paper, (1.4)–(1.9)),
`SmallGammaGeodesics.functional_tightness` (Theorem 1.2) and `SmallGammaGeodesics.geodesic_ae_unique`
(the a.s. unique constant-speed geodesic (1.3), with a measurable choice). The `example`s restate their
types verbatim from `SmallGammaGeodesics/Frozen/`; the result guide documents the correspondence with the
paper. -/

section SmallGammaGeodesicsRelease
open MeasureTheory Filter Topology Set
open scoped ENNReal

set_option pp.explicit false in
set_option pp.universes false in
#check SmallGammaGeodesics.deviation_scale

namespace SmallGammaGeodesics
open LQGMetric

example :
    ∀ (D : ℝ → DistC → ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P)
    (η : ℝ → Ω → C(unitInterval, ℂ))
    (_hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)),
    ∃ C γ₀ : ℝ, 0 < γ₀ ∧
      -- (1.4)
      (∀ γ ∈ Ioo (0 : ℝ) γ₀,
        ∫⁻ ω, ENNReal.ofReal (maxDev (η γ ω)) ∂P ≤ ENNReal.ofReal (C * γ ^ (2 / 3 : ℝ))) ∧
      -- (1.5)
      (∀ A : ℝ, 1 ≤ A → ∀ ε : ℝ, 0 < ε → ∀ᶠ γ in 𝓝[>] (0 : ℝ),
        P {ω | A * γ ^ (2 / 3 : ℝ) < maxDev (η γ ω)} ≤
          ENNReal.ofReal (C * (A ^ (-3 : ℝ) + A ^ (-4 : ℝ)) + ε)) ∧
      -- (1.6)
      (∀ γ ∈ Ioo (0 : ℝ) γ₀, ∀ a ∈ Ioc (0 : ℝ) 1,
        P {ω | maxDev (η γ ω) ≤ a * γ ^ (2 / 3 : ℝ)} ≤ ENNReal.ofReal (C * a ^ (3 / 5 : ℝ))) ∧
      -- (1.7)
      (∀ ε : ℝ, 0 < ε → ∃ a A : ℝ, 0 < a ∧ ∀ᶠ γ in 𝓝[>] (0 : ℝ),
        P {ω | ¬ (a ≤ maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ∧
          maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ≤ A)} ≤ ENNReal.ofReal ε) ∧
      -- (1.8)
      (∀ r ∈ Ioo (0 : ℝ) (3 / 5), ∃ K : ℝ, ∀ γ ∈ Ioo (0 : ℝ) γ₀,
        ∫⁻ ω, ENNReal.ofReal (maxDev (η γ ω) / γ ^ (2 / 3 : ℝ)) ^ (-r) ∂P ≤ ENNReal.ofReal K) ∧
      -- (1.9)
      (∀ ε : ℝ, 0 < ε → Tendsto (fun γ : ℝ => P {ω | ¬ (γ ^ (2 / 3 + ε) ≤ maxDev (η γ ω) ∧
          maxDev (η γ ω) ≤ γ ^ (2 / 3 - ε))}) (𝓝[>] 0) (𝓝 0)) :=
  deviation_scale

example :
    ∀ (D : ℝ → DistC → ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P)
    (η : ℝ → Ω → C(unitInterval, ℂ))
    (_hη : ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)),
    (∀ γ, 0 < γ → γ < 2 →
      AEMeasurable (fun ω => rescaledPath (γ ^ (2 / 3 : ℝ)) (η γ ω)) P) ∧
    (∀ ε : ℝ, 0 < ε → ∃ K : Set C(unitInterval, ℂ), IsCompact K ∧ ∀ᶠ γ in 𝓝[>] (0 : ℝ),
      P {ω | rescaledPath (γ ^ (2 / 3 : ℝ)) (η γ ω) ∉ K} ≤ ENNReal.ofReal ε) ∧
    TendstoInMeasure P (fun γ ω => horizDev (γ ^ (2 / 3 : ℝ)) (η γ ω)) (𝓝[>] 0) (fun _ => 0) :=
  functional_tightness

example :
    ∀ (D : ℝ → DistC → ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P),
    (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, ∃! η, Blueprint.IsGeod01 (D γ (h ω)) 0 1 η) ∧
    ∃ η : ℝ → Ω → C(unitInterval, ℂ), (∀ γ, Measurable (η γ)) ∧
      ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω) :=
  geodesic_ae_unique

end SmallGammaGeodesics
end SmallGammaGeodesicsRelease

assert_no_sorry SmallGammaGeodesics.deviation_scale
assert_no_sorry SmallGammaGeodesics.functional_tightness
assert_no_sorry SmallGammaGeodesics.geodesic_ae_unique
#print axioms SmallGammaGeodesics.deviation_scale
#print axioms SmallGammaGeodesics.functional_tightness
#print axioms SmallGammaGeodesics.geodesic_ae_unique

/-! ## Higher-dimensional exponential metrics: axiomatic existence and uniqueness

The frozen theorems `HigherDimLQGMetric.theorem12` (Theorem 1.2 of the source paper at `Q = Q(ξ)`: a strong
assignment exists, normalized LFPP converges to it for every nonnegative white-noise kernel, and it is unique up to a
deterministic constant) and `HigherDimLQGMetric.theorem14` (Theorem 1.4: uniqueness in the auxiliary weak class),
with `theorem14Sharp`, `strongUniqueness` and the non-vacuity theorem `sharpWeak_nonempty`. The `example`s restate
their types verbatim from `HigherDimLQGMetric/Frozen/`; the six sanity and characterization theorems are checked for
`sorry` and axioms. The result guide documents the correspondence with the paper. -/

section HigherDimLQGMetricRelease
open MeasureTheory Filter Topology Set

set_option pp.explicit false in
set_option pp.universes false in
#check HigherDimLQGMetric.theorem12

namespace HigherDimLQGMetric
open HigherDimLFPP (Rd)

-- Theorem 1.2 at `Q = Q(ξ)`, `Theorem12.lean`
example :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    (∃ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D ∧
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P →
        TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
          (fun ω => (D (h ω)).1)) ∧
    ∀ D D' : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d ξ (distExp d ξ) D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=
  theorem12

-- Theorem 1.4, `Theorem14.lean`
example :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ (D D' : DistRd d → ContMetric d) (c c' : ℝ → ℝ),
      IsWeakExpMetric d ξ D c → IsWeakExpMetric d ξ D' c' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=
  theorem14

-- Theorem 1.4 with the normalizers `r ^ (ξ Q)`, every `Q > √(2d)`, `Theorem14Sharp.lean`
example :
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsSharpWeakExpMetric d ξ Q D → IsSharpWeakExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=
  theorem14Sharp

-- Uniqueness of strong assignments, every `Q > √(2d)`, `StrongUniqueness.lean`
example :
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ Q D → IsStrongExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=
  strongUniqueness

-- Non-vacuity: the sharp weak class at `Q(ξ)` is nonempty, `SharpWeakNonempty.lean`
example :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ D : DistRd d → ContMetric d, IsSharpWeakExpMetric d ξ (distExp d ξ) D :=
  sharpWeak_nonempty

end HigherDimLQGMetric
end HigherDimLQGMetricRelease

assert_no_sorry HigherDimLQGMetric.theorem12
assert_no_sorry HigherDimLQGMetric.theorem14
assert_no_sorry HigherDimLQGMetric.theorem14Sharp
assert_no_sorry HigherDimLQGMetric.strongUniqueness
assert_no_sorry HigherDimLQGMetric.sharpWeak_nonempty
assert_no_sorry HigherDimLQGMetric.distExp_spec
assert_no_sorry HigherDimLQGMetric.subcritical_nonempty
assert_no_sorry HigherDimLQGMetric.normLGFLaw_spec
assert_no_sorry HigherDimLQGMetric.convKernel_smooth_integral
assert_no_sorry HigherDimLQGMetric.sphereAvg_spec
assert_no_sorry HigherDimLQGMetric.convMollify_spec
#print axioms HigherDimLQGMetric.theorem12
#print axioms HigherDimLQGMetric.theorem14
#print axioms HigherDimLQGMetric.theorem14Sharp
#print axioms HigherDimLQGMetric.strongUniqueness
#print axioms HigherDimLQGMetric.sharpWeak_nonempty
#print axioms HigherDimLQGMetric.distExp_spec
#print axioms HigherDimLQGMetric.subcritical_nonempty
#print axioms HigherDimLQGMetric.normLGFLaw_spec
#print axioms HigherDimLQGMetric.convKernel_smooth_integral
#print axioms HigherDimLQGMetric.sphereAvg_spec
#print axioms HigherDimLQGMetric.convMollify_spec
