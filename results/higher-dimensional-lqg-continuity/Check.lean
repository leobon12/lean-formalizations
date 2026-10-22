import HigherDimLQGContinuity.Frozen.Theorem11Metric
import HigherDimLQGContinuity.Frozen.Theorem11
import HigherDimLQGContinuity.Frozen.Theorem11Xi
import HigherDimLQGContinuity.Frozen.Prop18
import HigherDimLQGContinuity.Frozen.MedianOneStrongExists
import HigherDimLQGMetric.Frozen.NormLGFLawSpec
import Mathlib.Util.AssertNoSorry

/-! Almost sure continuity of the higher-dimensional LQG metric: the exact statements of the five frozen theorems
(Theorem 1.1 of the source paper with genuine metrics, `theorem11_metric`; its forms `theorem11` and `theorem11Xi`;
the parametrization `prop18`; the non-vacuity theorem `medianOneStrong_exists`), a derivation that the hypotheses of
the version clause of Theorem 1.1 can be met in dimension three, the frozen definitions, the section-level results,
absence of `sorry` and axioms, then an axiom audit of every declaration in the included `HigherDimLQGContinuity`,
`HigherDimLQGMetric`, `HigherDimLFPP`, `LQGMetric`, `LQGDimension`, `QuantumZipper` and `GaussianLQG` modules. The
result guide documents the correspondence with the paper. -/

open MeasureTheory Filter Topology Set

/-! ## The five frozen theorems: their types, restated verbatim from `HigherDimLQGContinuity/Frozen/` -/

#check HigherDimLQGContinuity.theorem11_metric
#check HigherDimLQGContinuity.theorem11
#check HigherDimLQGContinuity.theorem11Xi

namespace HigherDimLQGContinuity
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

-- Theorem 1.1 with genuine metrics, the [C] target (ruling N11), `Theorem11Metric.lean`
example :
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ γ : ℝ, 0 < γ → γ < Real.sqrt (2 * d) →
        ∀ ξ : ℝ, 0 < ξ → distExp d ξ = (d : ℝ) / γ + γ / 2 →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D γ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, (∀ γ₀ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∀ R : ℝ, 0 < R →
            Tendsto (fun γ => supDistLU d R (D γ (h ω)) (D γ₀ (h ω)))
              (𝓝[Ico (0 : ℝ) (Real.sqrt (2 * d))] γ₀) (𝓝 0)) ∧
          ∀ γ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∃ M : ContMetric d, M.1 = D γ (h ω) ∧ M.IsLength :=
  theorem11_metric

-- Theorem 1.1 in γ, `Theorem11.lean`
example :
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ γ : ℝ, 0 < γ → γ < Real.sqrt (2 * d) →
        ∀ ξ : ℝ, 0 < ξ → distExp d ξ = (d : ℝ) / γ + γ / 2 →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D γ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ γ₀ ∈ Ico (0 : ℝ) (Real.sqrt (2 * d)), ∀ R : ℝ, 0 < R →
          Tendsto (fun γ => supDistLU d R (D γ (h ω)) (D γ₀ (h ω)))
            (𝓝[Ico (0 : ℝ) (Real.sqrt (2 * d))] γ₀) (𝓝 0) :=
  theorem11

-- Theorem 1.1 in the Weyl parameter ξ, `Theorem11Xi.lean`
example :
    ∀ d : ℕ, 3 ≤ d →
    ∃ D : ℝ → DistRd d → C(Rd d × Rd d, ℝ),
      Measurable (Function.uncurry D) ∧
      (∀ g : DistRd d, D 0 g = euclidDistC d) ∧
      (∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
        ∀ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E → IsMedianOne d E →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P, D ξ (h ω) = (E (h ω)).1) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ ξ₀ ∈ xiRange d, ∀ R : ℝ, 0 < R →
          Tendsto (fun ξ => supDistLU d R (D ξ (h ω)) (D ξ₀ (h ω))) (𝓝[xiRange d] ξ₀) (𝓝 0) :=
  theorem11Xi

-- the parametrization (1.5), `Prop18.lean`
example :
    ∀ d : ℕ, 3 ≤ d →
      ContinuousOn (distExp d) (Ioi 0) ∧
      StrictAntiOn (distExp d) {ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ} ∧
      Tendsto (fun ξ => ξ * distExp d ξ) (𝓝[>] 0) (𝓝 1) ∧
      ∃ Ξ : ℝ → ℝ, Ξ 0 = 0 ∧
        StrictMonoOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        ContinuousOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        Ξ '' Ico 0 (Real.sqrt (2 * d)) = xiRange d ∧
        (∀ γ ∈ Ioo (0 : ℝ) (Real.sqrt (2 * d)), ∀ ξ : ℝ, 0 < ξ →
          (distExp d ξ = (d : ℝ) / γ + γ / 2 ↔ ξ = Ξ γ)) ∧
        Tendsto (fun γ => γ / Ξ γ) (𝓝[>] 0) (𝓝 (d : ℝ)) :=
  prop18

-- non-vacuity: median-one strong metrics exist, `MedianOneStrongExists.lean`
example :
    ∀ d : ℕ, 3 ≤ d → ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E ∧ IsMedianOne d E :=
  medianOneStrong_exists

/-! ## The hypotheses can be met: in dimension three, at `γ = 1`, the parameter `ξ = Ξ(1)` of `prop18` solves
`Q(ξ) = d/γ + γ/2` and is subcritical, a median-one strong metric exists there (`medianOneStrong_exists`), and the
normalized field exists (`normLGFLaw_spec`); the family of `theorem11_metric` is then almost surely equal, under the
law of the normalized field, to that metric at `γ = 1`, and is a length metric at every parameter -/

example : ∃ D : ℝ → DistRd 3 → C(Rd 3 × Rd 3, ℝ), ∃ (ξ : ℝ) (E : DistRd 3 → ContMetric 3),
    0 < ξ ∧ distExp 3 ξ = ((3 : ℕ) : ℝ) / 1 + 1 / 2 ∧
    IsStrongExpMetric 3 ξ (distExp 3 ξ) E ∧ IsMedianOne 3 E ∧
    IsProbabilityMeasure (normLGFLaw 3) ∧ IsNormalizedLGF id (normLGFLaw 3) ∧
    (∀ᵐ g ∂(normLGFLaw 3), D 1 g = (E g).1) ∧
    ∀ᵐ g ∂(normLGFLaw 3), ∀ γ ∈ Ico (0 : ℝ) (Real.sqrt (2 * ((3 : ℕ) : ℝ))),
      ∃ M : ContMetric 3, M.1 = D γ g ∧ M.IsLength := by
  obtain ⟨-, -, -, Ξ, hΞ0, hmono, -, himg, hiff, -⟩ := prop18 3 le_rfl
  have hs : (1 : ℝ) < Real.sqrt (2 * ((3 : ℕ) : ℝ)) := (Real.lt_sqrt zero_le_one).2 (by norm_num)
  have h0 : (0 : ℝ) ∈ Ico 0 (Real.sqrt (2 * ((3 : ℕ) : ℝ))) := ⟨le_rfl, zero_lt_one.trans hs⟩
  have h1 : (1 : ℝ) ∈ Ico 0 (Real.sqrt (2 * ((3 : ℕ) : ℝ))) := ⟨zero_le_one, hs⟩
  have hpos : 0 < Ξ 1 := by simpa [hΞ0] using hmono h0 h1 zero_lt_one
  have hmem : Ξ 1 ∈ xiRange 3 := by rw [← himg]; exact mem_image_of_mem Ξ h1
  have hsub : Real.sqrt (2 * ((3 : ℕ) : ℝ)) < distExp 3 (Ξ 1) := by
    rcases (mem_insert_iff.1 hmem) with h | h
    · exact absurd h hpos.ne'
    · exact h.2
  have hQ : distExp 3 (Ξ 1) = ((3 : ℕ) : ℝ) / 1 + 1 / 2 := (hiff 1 ⟨zero_lt_one, hs⟩ (Ξ 1) hpos).2 rfl
  obtain ⟨E, hE, hmed⟩ := medianOneStrong_exists 3 le_rfl (Ξ 1) hpos hsub
  obtain ⟨hprob, hnorm, -⟩ := normLGFLaw_spec 3 (by norm_num)
  obtain ⟨D, -, -, hver, hcont⟩ := theorem11_metric 3 le_rfl
  refine ⟨D, Ξ 1, E, hpos, hQ, hE, hmed, hprob, hnorm,
    hver 1 zero_lt_one hs (Ξ 1) hpos hQ E hE hmed (normLGFLaw 3) id hnorm, ?_⟩
  filter_upwards [hcont (normLGFLaw 3) id hnorm] with g hg using hg.2

end HigherDimLQGContinuity

assert_no_sorry HigherDimLQGContinuity.theorem11_metric
assert_no_sorry HigherDimLQGContinuity.theorem11
assert_no_sorry HigherDimLQGContinuity.theorem11Xi
assert_no_sorry HigherDimLQGContinuity.prop18
assert_no_sorry HigherDimLQGContinuity.medianOneStrong_exists
#print axioms HigherDimLQGContinuity.theorem11_metric
#print axioms HigherDimLQGContinuity.theorem11
#print axioms HigherDimLQGContinuity.theorem11Xi
#print axioms HigherDimLQGContinuity.prop18
#print axioms HigherDimLQGContinuity.medianOneStrong_exists

/-! ## The frozen definitions (the four of this library, and the main ones reused from the previous release) -/

#print HigherDimLQGContinuity.euclidDistC
#print HigherDimLQGContinuity.IsMedianOne
#print HigherDimLQGContinuity.supDistLU
#print HigherDimLQGContinuity.xiRange
#print HigherDimLQGMetric.IsStrongExpMetric
#print HigherDimLQGMetric.IsNormalizedLGF
#print HigherDimLQGMetric.normLGFLaw
#print HigherDimLQGMetric.distExp
#print HigherDimLQGMetric.ContMetric
#print HigherDimLQGMetric.ContMetric.IsLength

/-! ## The parts of the proof -/

-- §1: the parametrization (ϕ(ξ) = ξQ(ξ) is √(2d)-Lipschitz with ϕ(0) = 1, in place of [3]), median-one metrics
#check HigherDimLQGContinuity.phiXi_lipschitz
#check HigherDimLQGContinuity.prop18_holds
#check HigherDimLQGContinuity.medianOneStrong_holds
-- §2: Lemma 2.1 (uniform one-metric estimates, through Appendix A), Lemma 2.2, the covering (2.10), witnesses,
-- local events, connectors
#check HigherDimLQGContinuity.uniformEstimates_holds
#check HigherDimLQGContinuity.lemma22
#check HigherDimLQGContinuity.cover210_full
#check HigherDimLQGContinuity.isWitness_iff
#check HigherDimLQGContinuity.local_events_aeEventIn
#check HigherDimLQGContinuity.connector_of_good
-- §3: sewing (Lemma 3.1), Lemma 3.2, Proposition 3.3, Propositions 3.6 and 3.7
#check HigherDimLQGContinuity.lemma31a
#check HigherDimLQGContinuity.lemma31b
#check HigherDimLQGContinuity.lemma32
#check HigherDimLQGContinuity.prop33
#check HigherDimLQGContinuity.prop36
#check HigherDimLQGContinuity.prop37Shape_of
-- §4 (local field changes) and Proposition 3.5: Lemma 4.1′, the leads, the label network and labels, Lemma 4.3 and the
-- site certificate, Lemma 4.4, Proposition 4.5, the site event and Proposition 3.5
#check HigherDimLQGContinuity.Topology.lemma41_clearance
#check HigherDimLQGContinuity.Routing.exists_leads
#check HigherDimLQGContinuity.labelNet_spec
#check HigherDimLQGContinuity.exists_label_of_seedFav
#check HigherDimLQGContinuity.lemma43_forcing_holds
#check HigherDimLQGContinuity.lemma43_confine_holds
#check HigherDimLQGContinuity.siteCert_holds
#check HigherDimLQGContinuity.lemma44_pinned_holds
#check HigherDimLQGContinuity.prop45
#check HigherDimLQGContinuity.siteEvent_prob
#check HigherDimLQGContinuity.prop35_of
-- §5: the positive-parameter family, Lemma 5.1, the Euclidean endpoint, the metric-valued strengthening, assembly
#check HigherDimLQGContinuity.posVersion_of
#check HigherDimLQGContinuity.strongRotLaw_holds
#check HigherDimLQGContinuity.exists_pairingFrame
#check HigherDimLQGContinuity.concentration_of
#check HigherDimLQGContinuity.marginalEuclid_holds
#check HigherDimLQGContinuity.endpoint_of
#check HigherDimLQGContinuity.metricVersion_of
#check HigherDimLQGContinuity.theorem11Xi_of_parts
#check HigherDimLQGContinuity.theorem11_of
#check HigherDimLQGContinuity.theorem11_metric_of_parts
-- Appendix A: the uniform-in-ξ package of Ding–Gwynne–Zhuang, moments at the cutoff, the continuum estimates,
-- Theorem A.3 and Lemma 2.1
#check HigherDimLQGContinuity.uExpRate
#check HigherDimLQGContinuity.uniformDGZ_holds
#check HigherDimLQGContinuity.crudeLower
#check HigherDimLQGContinuity.wnUpperMoment_holds
#check HigherDimLQGContinuity.convUpperMoment
#check HigherDimLQGContinuity.convInvCross
#check HigherDimLQGContinuity.continuum_fatou
#check HigherDimLQGContinuity.continuum_escape
#check HigherDimLQGContinuity.lemma21_of

assert_no_sorry HigherDimLQGContinuity.phiXi_lipschitz
assert_no_sorry HigherDimLQGContinuity.uniformEstimates_holds
assert_no_sorry HigherDimLQGContinuity.prop33
assert_no_sorry HigherDimLQGContinuity.prop37Shape_of
assert_no_sorry HigherDimLQGContinuity.posVersion_of
assert_no_sorry HigherDimLQGContinuity.marginalEuclid_holds
assert_no_sorry HigherDimLQGContinuity.endpoint_of
assert_no_sorry HigherDimLQGContinuity.metricVersion_of
assert_no_sorry HigherDimLQGContinuity.uniformDGZ_holds
assert_no_sorry HigherDimLQGContinuity.lemma21_of
assert_no_sorry HigherDimLQGContinuity.theorem11_metric_of_parts
#print axioms HigherDimLQGContinuity.phiXi_lipschitz
#print axioms HigherDimLQGContinuity.uniformEstimates_holds
#print axioms HigherDimLQGContinuity.prop33
#print axioms HigherDimLQGContinuity.prop37Shape_of
#print axioms HigherDimLQGContinuity.posVersion_of
#print axioms HigherDimLQGContinuity.marginalEuclid_holds
#print axioms HigherDimLQGContinuity.endpoint_of
#print axioms HigherDimLQGContinuity.metricVersion_of
#print axioms HigherDimLQGContinuity.uniformDGZ_holds
#print axioms HigherDimLQGContinuity.lemma21_of
#print axioms HigherDimLQGContinuity.theorem11_metric_of_parts

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
    if (`HigherDimLQGContinuity).isPrefixOf m || (`HigherDimLQGMetric).isPrefixOf m ||
        (`HigherDimLFPP).isPrefixOf m || (`LQGMetric).isPrefixOf m || (`LQGDimension).isPrefixOf m ||
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
  logInfo m!"HIGHER_DIM_LQG_CONTINUITY_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
