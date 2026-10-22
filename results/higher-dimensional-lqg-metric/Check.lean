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
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLFPP.Field.Exists
import Mathlib.Util.AssertNoSorry

/-! Higher-dimensional exponential metrics: the exact statements of the eleven frozen theorems (Theorem 1.2
of the source paper at `Q = Q(ξ)`, Theorem 1.4, the uniqueness theorems `theorem14Sharp` and
`strongUniqueness`, and seven sanity and characterization theorems), a derivation that their hypotheses
can be met (a subcritical parameter in dimension three, a strong assignment, the normalized field and an
admissible kernel to which the LFPP clause applies, and an inhabitant of the weak class), the frozen
definitions, the proved literature inputs and section-level results, absence of `sorry` and axioms, then
an axiom audit of every declaration in the included `HigherDimLQGMetric`, `HigherDimLFPP`, `LQGMetric`,
`LQGDimension`, `QuantumZipper` and `GaussianLQG` modules. The result guide documents the correspondence
with the paper. -/

open MeasureTheory Filter Topology Set

/-! ## The eleven frozen theorems: their types, restated verbatim from `HigherDimLQGMetric/Frozen/` -/

#check HigherDimLQGMetric.theorem12
#check HigherDimLQGMetric.theorem14
#check HigherDimLQGMetric.theorem14Sharp
#check HigherDimLQGMetric.strongUniqueness

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

-- `Q(ξ)` exists, is kernel independent and unique, `DistExpSpec.lean`
example :
    ∀ (d : ℕ), 2 ≤ d → ∀ ξ : ℝ, 0 < ξ → ∀ Q : ℝ, IsDistanceExponent d ξ Q ↔ Q = distExp d ξ :=
  distExp_spec

-- The subcritical range contains an interval `(0, ξ₀)`, `SubcriticalNonempty.lean`
example :
    ∀ (d : ℕ), 2 ≤ d → ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, Real.sqrt (2 * d) < distExp d ξ :=
  subcritical_nonempty

-- The normalized LGF exists and its law is unique, `NormLGFLawSpec.lean`
example :
    ∀ (d : ℕ), 2 ≤ d → IsProbabilityMeasure (normLGFLaw d) ∧ IsNormalizedLGF id (normLGFLaw d) ∧
      ∀ μ : Measure (DistRd d), IsProbabilityMeasure μ → IsNormalizedLGF id μ → μ = normLGFLaw d :=
  normLGFLaw_spec

-- The kernel `K` of [1, Remark 1.1] is smooth with unit mass, `ConvKernelSmoothIntegral.lean`
example :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ ∫ x, convKernel κ x = 1 :=
  convKernel_smooth_integral

-- The limit defining the sphere average `h_r(z)` exists almost surely, `SphereAvgSpec.lean`
example :
    ∀ (d : ℕ), 2 ≤ d → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ u, h ω (bumpTest n (z + r • u)) ∂(unitSphereProb d))
          atTop (𝓝 (sphereAvg (h ω) r z)) :=
  sphereAvg_spec

-- The convolution `h * K_ε` exists almost surely, at every point, `ConvMollifySpec.lean`
example :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) :=
  convMollify_spec

/-! ## The hypotheses can be met: in dimension three there are a subcritical parameter, a strong
assignment, the normalized field and an admissible kernel, and the LFPP clause of Theorem 1.2 applies to
them; the weak class of Theorem 1.4 is inhabited -/

example : ∃ (ξ : ℝ) (D : DistRd 3 → ContMetric 3) (κ : Rd 3 → ℝ),
    0 < ξ ∧ Real.sqrt (2 * ((3 : ℕ) : ℝ)) < distExp 3 ξ ∧
    IsStrongExpMetric 3 ξ (distExp 3 ξ) D ∧ HigherDimLFPP.IsLFPPKernel κ ∧
    IsProbabilityMeasure (normLGFLaw 3) ∧ IsNormalizedLGF id (normLGFLaw 3) ∧
    TendstoInProbLU (normLGFLaw 3) (fun ε h => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε h) (𝓝[>] 0)
      (fun h => (D h).1) := by
  obtain ⟨ξ₀, hξ₀, hsub⟩ := subcritical_nonempty 3 (by norm_num)
  have hξ : 0 < ξ₀ / 2 := by positivity
  have hQ : Real.sqrt (2 * ((3 : ℕ) : ℝ)) < distExp 3 (ξ₀ / 2) := hsub (ξ₀ / 2) ⟨hξ, by linarith⟩
  obtain ⟨⟨D, hD, hlfpp⟩, -⟩ := theorem12 3 (ξ₀ / 2) le_rfl hξ hQ
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel 3
  obtain ⟨hprob, hnorm, -⟩ := normLGFLaw_spec 3 (by norm_num)
  have hin : IsLGFPlusBddCont (id : DistRd 3 → DistRd 3) (normLGFLaw 3) := hnorm.1.isLGFPlusBddCont
  exact ⟨ξ₀ / 2, D, κ, hξ, hQ, hD, hκ, hprob, hnorm, hlfpp κ hκ (normLGFLaw 3) id hin⟩

example : ∃ (ξ : ℝ) (D : DistRd 3 → ContMetric 3) (c : ℝ → ℝ),
    0 < ξ ∧ Real.sqrt (2 * ((3 : ℕ) : ℝ)) < distExp 3 ξ ∧ IsWeakExpMetric 3 ξ D c := by
  obtain ⟨ξ₀, hξ₀, hsub⟩ := subcritical_nonempty 3 (by norm_num)
  have hξ : 0 < ξ₀ / 2 := by positivity
  have hQ : Real.sqrt (2 * ((3 : ℕ) : ℝ)) < distExp 3 (ξ₀ / 2) := hsub (ξ₀ / 2) ⟨hξ, by linarith⟩
  obtain ⟨D, hD⟩ := sharpWeak_nonempty 3 (ξ₀ / 2) le_rfl hξ hQ
  exact ⟨ξ₀ / 2, D, _, hξ, hQ, hD⟩

end HigherDimLQGMetric

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

/-! ## The main frozen definitions (all 46 are in `HigherDimLQGMetric/Frozen/`) -/

#print HigherDimLQGMetric.IsStrongExpMetric
#print HigherDimLQGMetric.IsWeakExpMetric
#print HigherDimLQGMetric.IsSharpWeakExpMetric
#print HigherDimLQGMetric.TightOver
#print HigherDimLQGMetric.normalizedAtScale
#print HigherDimLQGMetric.IsWholeSpaceLGF
#print HigherDimLQGMetric.IsNormalizedLGF
#print HigherDimLQGMetric.IsLGFPlusCont
#print HigherDimLQGMetric.IsLGFPlusBddCont
#print HigherDimLQGMetric.sphereAvg
#print HigherDimLQGMetric.weylScale
#print HigherDimLQGMetric.distExp
#print HigherDimLQGMetric.IsDistanceExponent
#print HigherDimLQGMetric.aEps
#print HigherDimLQGMetric.lfppDist
#print HigherDimLQGMetric.convMollify
#print HigherDimLQGMetric.TendstoInProbLU

/-! ## The literature inputs, proved or replaced -/

-- [5] Krupski–Valov, replaced by codimension-two nonseparation (at most two arcs, d ≥ 3)
#check HigherDimLQGMetric.Topology.ns_arc
#check HigherDimLQGMetric.Topology.ns_tree
-- [6] kernel independence of the distance exponent, proved directly
#check HigherDimLQGMetric.kernel_indep
-- [7] Chen–Dafnis–Paouris, Gaussian Hölder inequality (Theorem 1(i))
#check HigherDimLQGMetric.Gauss.gaussianHolder_geom
#check HigherDimLQGMetric.Gauss.gaussianHolder_prob
-- (E4): the source's Lemma A.1 (Gaussian shell decoupling)
#check HigherDimLQGMetric.lemmaA1
-- (E3) and (E5) in the sharp class ([1] Props 3.13, 4.6, 4.11)
#check HigherDimLQGMetric.e3_sharp
#check HigherDimLQGMetric.comparison_criterion
#check HigherDimLQGMetric.e5_sharp_moment
-- [2] Ding–Gwynne–Zhuang §§4–6: comparison between scales and the real-ε adapter
#check HigherDimLQGMetric.DGZ.cor52Shape
#check HigherDimLQGMetric.DGZ.realEpsAdapter
-- [1] §3 (Theorem 1.3, (E1)): Gaussian-projection locality, locality of subsequential limits (Lemma 3.11),
-- metric shell input, bi-Lipschitz comparison, measurability, and the assembled statement
#check HigherDimLQGMetric.dMarkovRd
#check HigherDimLQGMetric.l7a_locality_of
#check HigherDimLQGMetric.l7c_metricShell
#check HigherDimLQGMetric.l7d_bilip
#check HigherDimLQGMetric.l7e_measurable
#check HigherDimLQGMetric.b3Goal_of
#check HigherDimLQGMetric.b3Goal'
-- [1] Proposition 4.2 and Theorem 1.6 ((E2): every weak assignment has the normalizers r ^ (ξ Q(ξ)))
#check HigherDimLQGMetric.prop42
#check HigherDimLQGMetric.theorem16
#check HigherDimLQGMetric.theorem16Shape'
-- the unconditional inputs of the final assembly ([1] Lemmas 3.7 and 3.16, [S] Lemma 10.3)
#check HigherDimLQGMetric.l6f_tightScales'
#check HigherDimLQGMetric.l7f_determined'
#check HigherDimLQGMetric.lemma103Shape'

/-! ## The parts of the proof -/

-- §§2–4: compactness, Hölder modulus, properness, collapse, routing, trap
#check HigherDimLQGMetric.lemma26_modulus
#check HigherDimLQGMetric.lemma27_proper
#check HigherDimLQGMetric.lemma31_collapse
#check HigherDimLQGMetric.lemma41_outer_routing_coordinates
#check HigherDimLQGMetric.lemma42_trap
-- §§5–8: frequency, fine-field amplification, traps, Cameron–Martin, counting
#check HigherDimLQGMetric.section5Package
#check HigherDimLQGMetric.fineFieldAmplification_of_lower_pair
#check HigherDimLQGMetric.trapProps_of_stable
#check HigherDimLQGMetric.lemma71
#check HigherDimLQGMetric.lemma81
#check HigherDimLQGMetric.lemma82
-- §8 Proposition 8.6; §9: the optimal constants, the macroscopic ratio, claim (32), closing the comparison gap
#check HigherDimLQGMetric.prop86
#check HigherDimLQGMetric.prop86Stmt
#check HigherDimLQGMetric.optUpperShape
#check HigherDimLQGMetric.macroRatioShape
#check HigherDimLQGMetric.claim32_of
#check HigherDimLQGMetric.theorem14Sharp_of_parts
-- §10: strong ⇒ weak, exact dilation covariance, full support, final assembly
#check HigherDimLQGMetric.lemma101
#check HigherDimLQGMetric.cor102Sharp_of
#check HigherDimLQGMetric.lemma103
#check HigherDimLQGMetric.cor104_of_inputs
#check HigherDimLQGMetric.theorem12_of_inputs
#check HigherDimLQGMetric.theorem14_of_inputs

assert_no_sorry HigherDimLQGMetric.Topology.ns_tree
assert_no_sorry HigherDimLQGMetric.kernel_indep
assert_no_sorry HigherDimLQGMetric.Gauss.gaussianHolder_prob
assert_no_sorry HigherDimLQGMetric.lemmaA1
assert_no_sorry HigherDimLQGMetric.e3_sharp
assert_no_sorry HigherDimLQGMetric.e5_sharp_moment
assert_no_sorry HigherDimLQGMetric.DGZ.realEpsAdapter
assert_no_sorry HigherDimLQGMetric.l7a_locality_of
assert_no_sorry HigherDimLQGMetric.l7d_bilip
assert_no_sorry HigherDimLQGMetric.b3Goal_of
assert_no_sorry HigherDimLQGMetric.b3Goal'
assert_no_sorry HigherDimLQGMetric.prop42
assert_no_sorry HigherDimLQGMetric.theorem16Shape'
assert_no_sorry HigherDimLQGMetric.prop86Stmt
assert_no_sorry HigherDimLQGMetric.theorem14Sharp_of_parts
assert_no_sorry HigherDimLQGMetric.lemma101
assert_no_sorry HigherDimLQGMetric.cor104_of_inputs
#print axioms HigherDimLQGMetric.Topology.ns_tree
#print axioms HigherDimLQGMetric.kernel_indep
#print axioms HigherDimLQGMetric.Gauss.gaussianHolder_prob
#print axioms HigherDimLQGMetric.lemmaA1
#print axioms HigherDimLQGMetric.e3_sharp
#print axioms HigherDimLQGMetric.e5_sharp_moment
#print axioms HigherDimLQGMetric.DGZ.realEpsAdapter
#print axioms HigherDimLQGMetric.l7a_locality_of
#print axioms HigherDimLQGMetric.l7d_bilip
#print axioms HigherDimLQGMetric.b3Goal_of
#print axioms HigherDimLQGMetric.b3Goal'
#print axioms HigherDimLQGMetric.prop42
#print axioms HigherDimLQGMetric.theorem16Shape'
#print axioms HigherDimLQGMetric.prop86Stmt
#print axioms HigherDimLQGMetric.theorem14Sharp_of_parts
#print axioms HigherDimLQGMetric.lemma101
#print axioms HigherDimLQGMetric.cor104_of_inputs

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
    if (`HigherDimLQGMetric).isPrefixOf m || (`HigherDimLFPP).isPrefixOf m || (`LQGMetric).isPrefixOf m ||
        (`LQGDimension).isPrefixOf m || (`QuantumZipper).isPrefixOf m || (`GaussianLQG).isPrefixOf m then
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
  logInfo m!"HIGHER_DIM_LQG_METRIC_AUDIT declarations={roots.size}; reachable={seen.size}; axioms={axioms.toList}"
