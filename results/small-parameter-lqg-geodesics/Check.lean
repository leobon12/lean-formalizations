import SmallGammaGeodesics.Frozen.DeviationScale
import SmallGammaGeodesics.Frozen.FunctionalTightness
import SmallGammaGeodesics.Frozen.GeodesicAeUnique
import Mathlib.Util.AssertNoSorry

/-! Small-parameter LQG geodesics: the exact statements of the three frozen theorems (Theorem 1.1 of the
source paper, (1.4)–(1.9); Theorem 1.2, tightness of the rescaled path and (1.11); and the a.s. unique
constant-speed geodesic (1.3) with a measurable choice), a derivation that their hypotheses can be met,
the three frozen definitions, the proved literature inputs (conformal covariance of the LQG metric for
maps conformal near the closure of a bounded domain, the near-identity conformal coupling, the dimension
input and the uniform moments that replace the paper's reference [5]), the section-level results of the
proof, absence of `sorry` and axioms, then an axiom audit of every declaration in the included
`SmallGammaGeodesics`, `LQGMetric`, `LQGDimension`, `QuantumZipper` and `GaussianLQG` modules. The
result guide documents the correspondence with the paper. -/

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-! ## Theorems 1.1, 1.2 and (1.3): their types, restated verbatim from `SmallGammaGeodesics/Frozen/` -/

#check SmallGammaGeodesics.deviation_scale
#check SmallGammaGeodesics.functional_tightness
#check SmallGammaGeodesics.geodesic_ae_unique

namespace SmallGammaGeodesics
open LQGMetric

-- Theorem 1.1, (1.4)–(1.9), `DeviationScale.lean`
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

-- Theorem 1.2, (1.10)–(1.11), `FunctionalTightness.lean`
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

-- (1.3): the a.s. unique constant-speed geodesic and a measurable choice, `GeodesicAeUnique.lean`
example :
    ∀ (D : ℝ → DistC → ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (_hh : IsNormalizedWPGFF h P),
    (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, ∃! η, Blueprint.IsGeod01 (D γ (h ω)) 0 1 η) ∧
    ∃ η : ℝ → Ω → C(unitInterval, ℂ), (∀ γ, Measurable (η γ)) ∧
      ∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω) :=
  geodesic_ae_unique

/-! ## The hypotheses can be met: a metric family, a normalized field and a measurable geodesic family
exist, and Theorem 1.1 applies to them -/

example :
    ∃ (D : ℝ → DistC → ContMetric) (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (h : Ω → DistC) (η : ℝ → Ω → C(unitInterval, ℂ)),
      (∀ γ, 0 < γ → γ < 2 → IsStrongLQGMetric γ (D γ)) ∧ IsNormalizedWPGFF h P ∧
      (∀ γ, Measurable (η γ)) ∧
      (∀ γ, 0 < γ → γ < 2 → ∀ᵐ ω ∂P, Blueprint.IsGeod01 (D γ (h ω)) 0 1 (η γ ω)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ a A : ℝ, 0 < a ∧ ∀ᶠ γ in 𝓝[>] (0 : ℝ),
        P {ω | ¬ (a ≤ maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ∧
          maxDev (η γ ω) / γ ^ (2 / 3 : ℝ) ≤ A)} ≤ ENNReal.ofReal ε := by
  have hex : ∀ γ : ℝ, ∃ D : DistC → ContMetric, 0 < γ → γ < 2 → IsStrongLQGMetric γ D := by
    intro γ
    by_cases hγ : 0 < γ ∧ γ < 2
    · obtain ⟨D, hD⟩ := GaussianLQG.exists_isCanonicalLQGMetric hγ.1 hγ.2
      exact ⟨D, fun _ _ => hD.1⟩
    · obtain ⟨D, _⟩ := GaussianLQG.exists_isCanonicalLQGMetric (γ := 1) one_pos one_lt_two
      exact ⟨D, fun h0 h2 => absurd ⟨h0, h2⟩ hγ⟩
  choose D hD using hex
  obtain ⟨Ω, _, P, hP, h, hh⟩ := LQGMetric.GFFExist.exists_normalizedWPGFF
  obtain ⟨η, hηm, hη⟩ := (geodesic_ae_unique D hD P h hh).2
  obtain ⟨C, γ₀, -, -, -, -, h17, -⟩ := deviation_scale D hD P h hh η hη
  exact ⟨D, Ω, inferInstance, P, hP, h, η, hD, hh, hηm, hη, h17⟩

end SmallGammaGeodesics

assert_no_sorry SmallGammaGeodesics.deviation_scale
assert_no_sorry SmallGammaGeodesics.functional_tightness
assert_no_sorry SmallGammaGeodesics.geodesic_ae_unique
#print axioms SmallGammaGeodesics.deviation_scale
#print axioms SmallGammaGeodesics.functional_tightness
#print axioms SmallGammaGeodesics.geodesic_ae_unique

/-! ## The three frozen definitions -/

#print SmallGammaGeodesics.maxDev
#print SmallGammaGeodesics.rescaledPath
#print SmallGammaGeodesics.horizDev

/-! ## The literature inputs, proved -/

-- [3] Gwynne–Miller, conformal covariance, Theorem 1.3 (intended form) for maps conformal on a
-- neighbourhood of the closure of a bounded domain, in coupled form, for every strong γ-LQG metric
#print SmallGammaGeodesics.CC.ConfCov
#print SmallGammaGeodesics.CC.MasterCCStrong
example : SmallGammaGeodesics.CC.MasterCCStrong :=
  SmallGammaGeodesics.CC.masterCCStrong_of_masterCC
    (SmallGammaGeodesics.CC.masterCC_of_masterCCLE SmallGammaGeodesics.CC.masterCCLE_holds)
-- its one-sided form ([3] Prop. 3.6), small-scale closeness ([3] Prop. 2.1), and the Möbius export
#check SmallGammaGeodesics.CC.masterCCLE_holds
#check SmallGammaGeodesics.CC.confSmallScale_holds
#check SmallGammaGeodesics.CC.mcInput_of_masterCC
-- the near-identity conformal coupling of whole-plane GFFs, and the coupling Lemma 4.2 built on it
#check SmallGammaGeodesics.NIC.nicInput_holds
#check SmallGammaGeodesics.lemma42_holds
-- [1] Ding–Gwynne, used only through (1.12)
#check SmallGammaGeodesics.dimension_input
-- the uniform moments that replace the paper's reference [5] in Lemma 2.1
#check SmallGammaGeodesics.uniformMomentInput_canonical
-- [2] Gwynne–Miller: every strong metric family is a.s. a constant multiple of a canonical one
#check SmallGammaGeodesics.exists_canonical_family

/-! ## The parts of the proof -/

-- §5, the upper bounds (5.14)–(5.15); §7, Proposition 7.1; §8, the scalar consequences (1.4)–(1.9)
#check SmallGammaGeodesics.upperBoundsXi_of_interfaces
#check SmallGammaGeodesics.lowerBound71_of_MC
#check SmallGammaGeodesics.devConcl_of_bounds
-- §6: tightness, the small-scale lower bound (Lemma 6.0) that replaces §6.3, and (1.11)
#check SmallGammaGeodesics.tightConcl_of_interfaces
#check SmallGammaGeodesics.smallScale_lower
#check SmallGammaGeodesics.tendstoInMeasure_horizDev
-- the reductions from an arbitrary probability space to the coordinate space
#check SmallGammaGeodesics.deviation_scale_of_internal
#check SmallGammaGeodesics.functional_tightness_of_internal

assert_no_sorry SmallGammaGeodesics.CC.masterCCLE_holds
assert_no_sorry SmallGammaGeodesics.CC.masterCC_of_masterCCLE
assert_no_sorry SmallGammaGeodesics.CC.masterCCStrong_of_masterCC
assert_no_sorry SmallGammaGeodesics.CC.confSmallScale_holds
assert_no_sorry SmallGammaGeodesics.CC.mcInput_of_masterCC
assert_no_sorry SmallGammaGeodesics.NIC.nicInput_holds
assert_no_sorry SmallGammaGeodesics.lemma42_holds
assert_no_sorry SmallGammaGeodesics.dimension_input
assert_no_sorry SmallGammaGeodesics.uniformMomentInput_canonical
assert_no_sorry SmallGammaGeodesics.exists_canonical_family
assert_no_sorry SmallGammaGeodesics.upperBoundsXi_of_interfaces
assert_no_sorry SmallGammaGeodesics.lowerBound71_of_MC
assert_no_sorry SmallGammaGeodesics.devConcl_of_bounds
assert_no_sorry SmallGammaGeodesics.tightConcl_of_interfaces
assert_no_sorry SmallGammaGeodesics.smallScale_lower
assert_no_sorry SmallGammaGeodesics.tendstoInMeasure_horizDev
#print axioms SmallGammaGeodesics.CC.masterCCLE_holds
#print axioms SmallGammaGeodesics.CC.masterCC_of_masterCCLE
#print axioms SmallGammaGeodesics.CC.masterCCStrong_of_masterCC
#print axioms SmallGammaGeodesics.CC.confSmallScale_holds
#print axioms SmallGammaGeodesics.CC.mcInput_of_masterCC
#print axioms SmallGammaGeodesics.NIC.nicInput_holds
#print axioms SmallGammaGeodesics.lemma42_holds
#print axioms SmallGammaGeodesics.dimension_input
#print axioms SmallGammaGeodesics.uniformMomentInput_canonical
#print axioms SmallGammaGeodesics.exists_canonical_family
#print axioms SmallGammaGeodesics.upperBoundsXi_of_interfaces
#print axioms SmallGammaGeodesics.lowerBound71_of_MC
#print axioms SmallGammaGeodesics.devConcl_of_bounds
#print axioms SmallGammaGeodesics.tightConcl_of_interfaces
#print axioms SmallGammaGeodesics.smallScale_lower
#print axioms SmallGammaGeodesics.tendstoInMeasure_horizDev

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
    if (`SmallGammaGeodesics).isPrefixOf m || (`LQGMetric).isPrefixOf m || (`LQGDimension).isPrefixOf m ||
        (`QuantumZipper).isPrefixOf m || (`GaussianLQG).isPrefixOf m then
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
  logInfo m!"SMALL_GAMMA_GEODESICS_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
