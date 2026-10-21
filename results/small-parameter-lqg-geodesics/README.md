# Small-parameter LQG geodesics: deviation and functional tightness

Lean formalization of **Theorems 1.1 and 1.2** of *Small-parameter LQG geodesics: deviation and
functional tightness* (12 October 2026; [AI research
paper](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/small-parameter-lqg-geodesics.pdf),
AI-generated and unrefereed), developed under Leonardo Bonanno's direction with AI assistance.

The formalization covers **both theorems in full, with no assumptions**: the two-thirds deviation scale
of the γ-LQG geodesic from 0 to 1, all of (1.4)–(1.9), and the tightness of the rescaled path in
C([0,1], ℝ²) together with (1.11). The only hypotheses are the definitions of the objects: a γ-LQG
metric for each γ ∈ (0,2), the normalized whole-plane GFF, and the constant-speed geodesic from 0 to 1.
The paper cites five works for its inputs. Ding–Gwynne's dimension bounds [1], Gwynne–Miller's existence
and uniqueness of the metric [2], and the uniqueness of geodesics between fixed points that the paper
takes from their confluence paper [4] are theorems of earlier releases. Kavvadias' estimates [5] are not
needed. **Gwynne–Miller's conformal covariance of the LQG metric [3], which no earlier release
contained, is proved here** for maps that are conformal on a neighbourhood of the closure of a bounded
domain, the case the paper uses.

[Theorem 1.1](../../SmallGammaGeodesics/Frozen/DeviationScale.lean#L30-L57) · [Theorem
1.2](../../SmallGammaGeodesics/Frozen/FunctionalTightness.lean#L34-L45) · [Frozen
definitions](../../SmallGammaGeodesics/Frozen/) · [Proofs](../../SmallGammaGeodesics/Assembly/) ·
[Conformal covariance](../../SmallGammaGeodesics/CC/) · [Focused certificate](Check.lean) · [Verification
record](verification.json)

## The theorems

Let h be a whole-plane Gaussian free field normalized so that its average on the unit circle is zero, and
for γ ∈ (0,2) let D_h^γ be the γ-LQG metric. Let P_γ : [0,1] → ℂ be the almost surely unique
D_h^γ-geodesic from 0 to 1, parametrized at constant metric speed, D_h^γ(0, P_γ(t)) = t·D_h^γ(0,1) (1.3),
and let M_γ = max_t dist(P_γ(t), [0,1]) be its largest Euclidean distance from the segment [0,1].

**Theorem 1.1** (the two-thirds deviation scale). There are deterministic constants C < ∞ and γ₀ > 0 such
that:

- **(1.4)** E M_γ ≤ C γ^{2/3} for 0 < γ < γ₀;
- **(1.5)** for every A ≥ 1, lim sup_{γ→0} P[M_γ > A γ^{2/3}] ≤ C(A^{−3} + A^{−4});
- **(1.6)** P[M_γ ≤ a γ^{2/3}] ≤ C a^{3/5}, uniformly for 0 < γ < γ₀ and 0 < a ≤ 1;
- **(1.7)** for every ε > 0 there are a > 0, A < ∞ and γ_ε > 0 with P[a ≤ M_γ/γ^{2/3} ≤ A] ≥ 1 − ε for
  0 < γ < γ_ε;
- **(1.8)** sup_{0<γ<γ₀} E[(M_γ/γ^{2/3})^{−r}] < ∞ for every r ∈ (0, 3/5);
- **(1.9)** P[γ^{2/3+ε} ≤ M_γ ≤ γ^{2/3−ε}] → 1 as γ → 0, for every ε > 0.

**Theorem 1.2** (functional tightness). The paths X_γ(t) = (P_γ(t) − t)/γ^{2/3}, t ∈ [0,1], of (1.10) are
tight in C([0,1], ℝ²) with the uniform topology as γ → 0, and **(1.11)** sup_{t∈[0,1]} |Re P_γ(t) −
t|/γ^{2/3} → 0 in probability.

The proof declarations are `SmallGammaGeodesics.deviation_scale` and
`SmallGammaGeodesics.functional_tightness`. Their statements, copied from
[`SmallGammaGeodesics/Frozen/DeviationScale.lean`](../../SmallGammaGeodesics/Frozen/DeviationScale.lean#L30-L57)
and
[`SmallGammaGeodesics/Frozen/FunctionalTightness.lean`](../../SmallGammaGeodesics/Frozen/FunctionalTightness.lean#L34-L45)
(inside `namespace SmallGammaGeodesics`, with `open MeasureTheory Filter Topology Set`, `open scoped
ENNReal` and `open LQGMetric`), are:

```lean
theorem deviation_scale :
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

theorem functional_tightness :
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
```

Their proofs are `by exact SmallGammaGeodesics.deviation_scale_impl` and `by exact
SmallGammaGeodesics.functional_tightness_impl`
([`Assembly/Deviation.lean`](../../SmallGammaGeodesics/Assembly/Deviation.lean),
[`Assembly/Tightness.lean`](../../SmallGammaGeodesics/Assembly/Tightness.lean)). The statements hold for
every metric family, every normalized field on any probability space and every family η that is almost
surely the constant-speed geodesic. They were frozen and audited independently against the paper before
the proofs were complete. Sealing changed only the one-line proof bodies; a hash of the elaborated
statements confirms that they are unchanged.

A third frozen theorem,
[`geodesic_ae_unique`](../../SmallGammaGeodesics/Frozen/GeodesicAeUnique.lean#L31-L38), is the paper's
(1.3): for each γ ∈ (0,2), almost surely the constant-speed geodesic from 0 to 1 exists and is unique,
and some family of measurable choices is almost surely that geodesic. So the hypotheses of the two
theorems can be met, and all families η they allow agree almost surely. [`Check.lean`](Check.lean)
restates the three statements verbatim, checks that the frozen declarations prove them, and derives from
`geodesic_ae_unique` and the existence of the metric and of the field an actual family to which Theorem
1.1 applies.

## The frozen definitions

Each project definition in the statements is frozen in its own file under
[`SmallGammaGeodesics/Frozen/`](../../SmallGammaGeodesics/Frozen/). The other names come from Mathlib and
from the [LQG metric release](../lqg-metric/).

| Paper | Lean | Definition |
| --- | --- | --- |
| M_γ, §1 | [`maxDev η`](../../SmallGammaGeodesics/Frozen/MaxDev.lean#L27) | The supremum over t ∈ [0,1] of the Euclidean distance from η(t) to the segment from 0 to 1. The function is continuous on a compact set, so the supremum is attained. |
| X_γ, (1.10) | [`rescaledPath s η`](../../SmallGammaGeodesics/Frozen/RescaledPath.lean#L25) | The continuous path t ↦ (η(t) − t)/s in `C(unitInterval, ℂ)`, used with s = γ^{2/3}. |
| the quantity in (1.11) | [`horizDev s η`](../../SmallGammaGeodesics/Frozen/HorizDev.lean#L24) | The supremum over t ∈ [0,1] of the absolute value of Re η(t) − t, divided by s, used with s = γ^{2/3}. |
| the γ-LQG metric | [`IsStrongLQGMetric γ D`](../../LQGMetric/Statement/LQGMetric.lean#L36) | Gwynne–Miller's strong γ-LQG metric: a measurable map h ↦ D_h to continuous metrics on ℂ satisfying Axioms I–IV (length space, locality, Weyl scaling, coordinate change) for every whole-plane GFF plus a continuous function. |
| the field h | [`IsNormalizedWPGFF h P`](../../LQGMetric/Statement/GFF.lean#L47) | A whole-plane GFF (its pairings with mean-zero test functions form a centred Gaussian process with covariance ∬ φ(x)(−log‖x − y‖)ψ(y) dx dy) whose average on the unit circle is 0 almost surely. |
| P_γ, (1.3) | [`Blueprint.IsGeod01 D 0 1 η`](../../LQGMetric/Blueprint/M2Defs.lean#L82) | η(0) = 0, η(1) = 1 and D(η(s), η(t)) = ‖t − s‖·D(0,1) for all s, t ∈ [0,1]: a geodesic from 0 to 1 at constant speed. |

## Correspondence with Theorems 1.1 and 1.2

Each clause of `deviation_scale` carries the paper's equation number as a comment. In Lean, with type
ascriptions and the coercion `ENNReal.ofReal` omitted:

- **(1.4)**: `∫⁻ ω, maxDev (η γ ω) ∂P ≤ C * γ ^ (2/3)` for γ ∈ (0, γ₀). The expectation is a lower
  Lebesgue integral, which is meaningful without any measurability assumption.
- **(1.5)**: for A ≥ 1 and every ε > 0, eventually as γ ↓ 0, `P {ω | A * γ ^ (2/3) < maxDev (η γ ω)} ≤
  C * (A ^ (-3) + A ^ (-4)) + ε`. This ε-slack form is equivalent to the bound on the lim sup in [0,∞].
- **(1.6)**: `P {ω | maxDev (η γ ω) ≤ a * γ ^ (2/3)} ≤ C * a ^ (3/5)` for γ ∈ (0, γ₀) and a ∈ (0,1].
- **(1.7)**: for every ε > 0 there are a > 0 and A with, eventually as γ ↓ 0, the probability of the
  complement of {a ≤ M_γ/γ^{2/3} ≤ A} at most ε. "Probability at least 1 − ε" is stated for the
  complement, which needs no measurability; the two agree for measurable events.
- **(1.8)**: for r ∈ (0, 3/5) there is K with `∫⁻ ω, (maxDev (η γ ω) / γ ^ (2/3)) ^ (-r) ∂P ≤ K` for γ ∈
  (0, γ₀). The power is taken in [0,∞], where 0^{−r} = ∞, so the bound also says that M_γ > 0 almost
  surely.
- **(1.9)**: for every ε > 0, the probability that γ^{2/3+ε} ≤ M_γ ≤ γ^{2/3−ε} fails tends to 0 as γ ↓ 0.

The three clauses of `functional_tightness`:

- **measurability**: for each γ ∈ (0,2), ω ↦ X_γ is almost everywhere measurable, so X_γ has a law on
  C([0,1], ℂ);
- **tightness (1.10)**: for every ε > 0 there is a compact set K of paths with P[X_γ ∉ K] ≤ ε for all
  sufficiently small γ > 0;
- **(1.11)**: `TendstoInMeasure P (fun γ ω => horizDev (γ ^ (2/3)) (η γ ω)) (𝓝[>] 0) (fun _ => 0)`,
  convergence to 0 in probability as γ ↓ 0.

## Scope and statement conventions

- **The metric.** `IsStrongLQGMetric γ` is Gwynne–Miller's strong γ-LQG metric with ξ = γ/d_γ, as
  formalized in the [LQG metric release](../lqg-metric/). By their uniqueness theorem
  (`LQGMetric.theorem12_proved`) a strong metric is almost surely a deterministic positive multiple of
  the canonical one, and geodesics, M_γ and X_γ do not change when the metric is multiplied by a constant
  ([`exists_canonical_family`](../../SmallGammaGeodesics/Core/Setup.lean#L56)). So quantifying over every
  family `D` speaks about the paper's metric, whatever its normalization. The metrics for different γ are
  applied to the same field, as in the paper.
- **The field.** `IsNormalizedWPGFF h P` is exactly the paper's field: its covariance is (1.2) for the
  Dirichlet inner product (1.1) and its average on ∂𝔻 is 0. Probability spaces range over Lean's `Type`
  universe.
- **The geodesic.** The theorems quantify over **every** family η that, for each γ ∈ (0,2), is almost
  surely the constant-speed geodesic from 0 to 1. No measurability of η is assumed, and no object is
  selected by choice. `geodesic_ae_unique` shows that such families exist and agree almost surely.
- **Constants.** In Lean, C and γ₀ are chosen after the metric family, the probability space, the field
  and the path family. This is equivalent to the paper's deterministic constants, because the joint law
  of the field and the geodesic is the same for every instance
  ([`deviation_scale_of_internal`](../../SmallGammaGeodesics/Assembly/Reduction.lean#L66) transfers every
  statement from one coordinate space).
- **Tightness over a continuum.** Theorem 1.2 is stated for γ ↓ 0 through all real γ, not along
  sequences, in the explicit compact-set form above, with the measurability of X_γ as a separate clause.
  `C(unitInterval, ℂ)` carries the compact-open topology, which is the topology of uniform convergence,
  and ℂ is ℝ² with the Euclidean norm.
- **Junk values.** Expectations are lower Lebesgue integrals, negative moments live in [0,∞], and every
  real power has a positive base where it is used. `maxDev` and `horizDev` are suprema of continuous
  functions on [0,1], so they are attained and finite.
- **Remarks not frozen.** The paper's remark that every subsequential weak limit of M_γ/γ^{2/3} is finite
  and strictly positive follows from (1.7) by the portmanteau theorem; (1.7) is the stronger statement,
  as the paper says. The paper asserts no uniqueness of a subsequential limiting law, and neither does
  the formalization.

## No assumptions: the literature inputs

The paper's Section 2.1 imports results from five works. Each is a theorem here or is not needed:

| Paper's input | What the paper uses | In this release |
| --- | --- | --- |
| [1] Ding–Gwynne, dimension bounds | only (1.12): ξ ∼ γ/2 and the bound on p_γ − 1 by Cξ | [`dimension_input`](../../SmallGammaGeodesics/Core/Setup.lean#L113), from `GaussianLQG.dimensionInput_holds` of the [Gaussian LQG distance release](../gaussian-lqg-distance/), which gives d_γ = 2 + O(γ) |
| [2] Gwynne–Miller, existence and uniqueness | locality, Weyl scaling, coordinate change, bounded compactness, existence of geodesics | theorems of the [LQG metric release](../lqg-metric/) (`LQGMetric.theorem11_proved`, `LQGMetric.theorem12_proved`); the pathwise form of locality used in Sections 4.2 and 7 (fields that agree on U give the same internal metric on U) is proved here ([`ae_internal_eq_of_ae_restrictTo_eq`](../../SmallGammaGeodesics/CC/UniversalLocality.lean#L198)) |
| [3] Gwynne–Miller, conformal covariance, Theorem 1.3 | the one-sided comparison (5.3) for near-identity probe maps and the two-sided covariance for Möbius maps in Section 7 | **proved here** for maps conformal near the closure of a bounded domain (next section) |
| [4] Gwynne–Miller, confluence, Lemma 2.2 | uniqueness of the geodesic between two fixed points | from the LQG metric release, through Miller–Qian's theorem for weak metrics, with the needed estimate of Dubédat–Falconet–Gwynne–Pfeffer–Sun proved there ([`ae_existsUnique_geod01`](../../SmallGammaGeodesics/Geodesic/Basic.lean#L40)); a measurable choice of the geodesic is `LQGMetric.exists_measurable_geodSel` |
| [5] Kavvadias, Theorem 1.7 and Lemmas 3.4, 5.4 | only inside the proof of the paper's Lemma 2.1 (moments, escape radius, Hölder bound) | **not needed**: Lemma 2.1 is replaced by the certified uniform moments of the Gaussian LQG distance release ([`uniformMomentInput_canonical`](../../SmallGammaGeodesics/Core/Setup.lean#L81)), its localization estimates and its quantitative Euclidean limit `GaussianLQG.Setup.euclidApprox`, which is stronger than Kavvadias' Theorem 1.7 |

The paper's other unstated tools are proved or replaced. Lusin's theorem, which Mathlib lacks, is proved
([`exists_isCompact_measure_compl_lt_continuousOn`](../../SmallGammaGeodesics/CC/Lusin.lean#L60)).
Bernstein's inequality for trigonometric polynomials, also absent from Mathlib, is replaced by a discrete
sampling lemma ([`lemma41_sampling`](../../SmallGammaGeodesics/Probes/Sampling.lean#L448)). Pinsker's
inequality is replaced by a χ² Cameron–Martin bound on total variation
([`abs_lawPair0_addFun_sub_le_sqrt_two`](../../SmallGammaGeodesics/Lower/TV.lean#L67)).

### Conformal covariance is proved

The paper uses (2.1), Gwynne–Miller's Theorem 1.3, in two places: Section 5 compares the geodesic with
its image under probe maps z ↦ z + iθH(z) that fix 0 and 1, and Section 7 uses disjoint Möbius images of
a thin tube. Neither Weyl scaling nor affine coordinate change can bend the segment while fixing its
endpoints, so the input cannot be bypassed. It is proved in
[`SmallGammaGeodesics/CC/`](../../SmallGammaGeodesics/CC/) (54 files) for every map ϕ that is
holomorphic and injective on an open set containing the closure of a bounded open set V
([`IsConfNbhd`](../../SmallGammaGeodesics/Core/Interfaces.lean#L34)), in coupled form
([`ConfCov`](../../SmallGammaGeodesics/Core/Interfaces.lean#L66)). If h and h̄ are whole-plane GFFs and
f is a continuous random function with h∘ϕ⁻¹ + Q log‖(ϕ⁻¹)′‖ = h̄ + f on ϕ(V)
([`IsConfCoupling`](../../SmallGammaGeodesics/Core/Interfaces.lean#L49)), then almost surely D_h(z, w;
V) = D_{h̄+f}(ϕ(z), ϕ(w); ϕ(V)) for all z, w ∈ V, where the semicolon denotes internal metrics. This
holds for every strong γ-LQG metric and every γ ∈ (0,2)
([`MasterCCStrong`](../../SmallGammaGeodesics/Core/Interfaces.lean#L104), proved in `Check.lean` from
the theorems below).

The proof follows Gwynne–Miller's own axiomatic argument, with four simplifications:

1. **Small-scale closeness** ([3] Proposition 2.1,
   [`confSmallScale_holds`](../../SmallGammaGeodesics/CC/Prop21.lean#L70)). Instead of total-variation
   convergence, Prokhorov's theorem and Koebe distortion, the proof zooms in at a point and couples the
   field with its conformal image by a near-identity conformal coupling of whole-plane GFFs
   ([`nicInput_holds`](../../SmallGammaGeodesics/NIC/Main.lean#L39)), then passes equal laws through the
   locality functional of the metric with Lusin's theorem.
2. **One direction of the bi-Lipschitz bound** on the domain ([3] Proposition 3.1 and Lemma 3.5,
   [`confBiLipLE_of_smallScale`](../../SmallGammaGeodesics/CC/BiLip.lean#L158)), by an annulus iteration
   of the LQG metric release, without the joint-locality theory.
3. **The optimal constant is never defined.** [3] Proposition 3.6 is formalized as an improvement step
   ([`confImprove_of_goodAnnulus`](../../SmallGammaGeodesics/CC/Improve.lean#L305)), with the
   good-annulus estimates of [3] Lemmas 3.8–3.10
   ([`goodAnnulusInput_holds`](../../SmallGammaGeodesics/CC/GoodAnnulusProb.lean#L96)) and a covering
   lemma ([`coverLemma_uniform`](../../SmallGammaGeodesics/CC/Cover.lean#L237)). Iterating it from the
   bi-Lipschitz constant gives the one-sided comparison
   ([`confCovLE_of_biLip_improve`](../../SmallGammaGeodesics/Core/Interfaces.lean#L244),
   [`masterCCLE_holds`](../../SmallGammaGeodesics/CC/MasterLE.lean#L37)).
4. **Two-sided by reversal.** Reversing the coupling gives the other inequality
   ([`reversal_holds`](../../SmallGammaGeodesics/CC/Reversal.lean#L99),
   [`masterCC_of_masterCCLE`](../../SmallGammaGeodesics/CC/Master.lean#L66)), and Gwynne–Miller
   uniqueness extends it from the canonical metric to every strong metric
   ([`masterCCStrong_of_masterCC`](../../SmallGammaGeodesics/CC/Master.lean#L71)).

Section 7 uses the Möbius case modulo constants, as a functional of the field on the image domain
([`mcInput_of_masterCC`](../../SmallGammaGeodesics/CC/Sigma0MC.lean#L129)). The same near-identity
coupling proves the paper's coupling Lemma 4.2
([`lemma42_holds`](../../SmallGammaGeodesics/Upper/Lemma42Holds.lean#L16)), replacing its
Green's-function and conformal-radius computations. It needs a square root of a positive operator on a
real Hilbert space, built from a binomial series because Mathlib's operator square root is only for
complex operator algebras.

Five errata in [3] were found and corrected. As printed, Theorem 1.3 assumes "ϕ : ℂ → U conformal", which
is vacuous for U ≠ ℂ and allows only affine maps for U = ℂ; the intended hypothesis is Axiom IV of its
Definition 1.1, ϕ : U → Ũ, as the paper's (2.1) uses it. Lemmas 2.6 and 2.7 must translate by ϕ(z), not
z; otherwise ϕ_n(0) is unbounded and the hypothesis ϕ_n(0) = 0 of Lemma 2.3 fails. The other three, a
sign in the proof of Theorem 1.3, the domain in the conclusion of Theorem 3.4 and a notation slip in the
proof of Lemma 2.4, do not affect the argument.

## Differences from the paper

### Tightness over a continuum

Section 6.3 deduces tightness from the principle that "asymptotically vanishing distance from a tight
family preserves tightness". That holds along sequences but is false for a family indexed by a continuum
of γ, which is what γ → 0 means here. The proof instead uses a new small-scale lower bound for the
normalized metric, uniform in small γ (Lemma 6.0, D̂(z, w) ≥ ‖z − w‖^{5/4} at small scales,
[`smallScale_lower`](../../SmallGammaGeodesics/Tight/SmallScale.lean#L527)). It gives a deterministic
modulus of continuity for the geodesic
([`path_modulus_of_smallScale`](../../SmallGammaGeodesics/Tight/Modulus.lean#L130)), and the
Arzelà–Ascoli theorem gives the compact set directly
([`tightConcl_of_interfaces`](../../SmallGammaGeodesics/Tight/Main.lean#L48)). The frozen files cite this
choice as ruling G12. The horizontal estimate (1.11) is proved separately, without the probes
([`tendstoInMeasure_horizDev`](../../SmallGammaGeodesics/Tight/Coord.lean#L88)).

### Fixed moments instead of growing moments

The paper's Lemma 2.2 gives the Euclidean error of the normalized metric at rate ξ log(1/ξ) with
exponential tails, from moments of growing order (2.10)–(2.12). The formalization uses only moments of
fixed order ([`euclidFine`](../../SmallGammaGeodesics/Inputs/EuclidFine.lean#L257)): the error is at most
ξ^{99/100} off an event of polynomially small probability. Lemma 3.2 then holds as E Z² ≤ Cξ²(m +
ξ^{99/100} L) instead of Cξ²(m + ξL²)
([`residualVariance`](../../SmallGammaGeodesics/Variance/Residual.lean#L636)), and every exponent of
Sections 5 and 6 was rechecked with the weaker term; the binding constraint, in (5.9), needs an exponent
above 281/288. The metric is normalized by the mean of log D(0,1) rather than by the median, which the
paper uses only to bound that mean; M_γ and X_γ do not depend on the normalization.

### Other corrections

The proof follows a corrected rewrite of the paper, prepared from independent section-by-section audits;
its errata list has more than 80 items. Apart from explicit constants and quantifiers, the main ones are:

- **Section 4.** The probe envelope of Lemma 4.1, which the paper does not define, is given explicitly; a
  natural minimum form takes a junk value where the distance vanishes. Poisson summation is replaced by
  summation by parts, and Bernstein's inequality by the sampling lemma above. Lemma 4.2 is restated with
  an explicit strip and rectangles, the pullback defined on the injectivity strip, and the pairing
  identity that (5.4) uses.
- **Section 5.** The comparison (5.3) is derived from the one-sided conformal covariance on a subdomain,
  with a Weyl comparison along the bent path, which is not a geodesic of any metric involved. The
  residuals of (5.4) are one Borel functional of the field, and their second moments are transferred
  explicitly between the coupling spaces and a fixed coordinate space.
- **Section 7.** Windows of radius 2r replace the paper's 6r/5, which is needed for a positive gap; the
  local Möbius invariance of the GFF law is stated modulo constants; the constants are explicit (R₀ =
  10⁻³, K = 100, r* = 2·10^{−15/2}).
- **Citations.** The lower bound d_γ > 2 is [1, Theorem 1.1], not Theorem 1.2, and it is not used;
  rotation invariance is [2, Corollary 1.3].

### Not formalized

- The growing-moment estimates (2.10)–(2.12), the rate ξ log(1/ξ) in Lemma 2.2 and its exponential tail
  (not needed, see above).
- The subsequential-limit remark after (1.8), which follows from (1.7).
- Theorem 1.3 of [3] beyond maps conformal on a neighbourhood of the closure of a bounded domain, and its
  zero-boundary form.
- The variant of the theorems for a whole-plane GFF with another additive normalization, which follows by
  Weyl scaling.
- Numerical values of the constants.

## Verification

The export adds **140 modules**, copied byte-for-byte from development commit
`cda0ca791aa47c86fb1f8f99835b702d17ba244b` (the release commit; both theorems were sealed in
`d7b7ea0af`, and the exported files differ from that commit only in one documentation comment
(`SmallGammaGeodesics/Upper/Interfaces.lean`)): the 138 `SmallGammaGeodesics` modules and two aggregator
modules of the Gaussian LQG distance library, `GaussianLQG` (its root file `GaussianLQG.lean`, which
`SmallGammaGeodesics.Core.Setup` imports) and `GaussianLQG.Uniform.RSW`. The two declare nothing and
import only modules that were already released. The local import closure of the three frozen theorems
has **3,710 modules**: 138 SmallGammaGeodesics, 2,362 LQGMetric, 931 QuantumZipper, 169 GaussianLQG and
110 LQGDimension. The other 3,570 were already part of this release and are byte-identical. Lean
`v4.34.0-rc2` and Mathlib `a4c8ef0a69f52ec80525d5086bb3542f4660faaf` match the rest of the release.

- **Kernel replay (development workspace).** `lake env leanchecker --fresh SmallGammaGeodesics`
  re-checked, in a fresh environment, every declaration in the import closure of the development root
  module, which imports the three frozen theorem modules, Mathlib included. It **exited with code 0**,
  with no errors, on 21 October 2026 (11:10–11:22 CEST, 12 min 50 s), on the Lean sources of commit
  `cda0ca791`.
- **Fresh build and focused certificate (this export).** The 140 new modules were **compiled afresh from
  the exported files**, with the public verifier's per-module settings. The 3,570 previously released
  dependencies were reused from a cache after all 3,710 source files were checked byte-for-byte.
  [`Check.lean`](Check.lean) was then compiled afresh and **passed**. It checks the verbatim statements
  of the three theorems, derives an actual family to which Theorem 1.1 applies, prints the three
  definitions, and checks the conformal covariance, the near-identity coupling, the dimension and moment
  inputs and the section-level results. It rejects `sorry` and audits **55,178 project declarations and
  139,923 reachable declarations**, allowing only `propext`, `Classical.choice` and `Quot.sound`. See
  [verification.json](verification.json). `leanchecker --fresh` then replayed this build, through a
  scratch module that imports the three frozen theorem modules, and exited with code 0 (12 min 7 s).
- The [public workflow](https://github.com/leobon12/lean-formalizations/actions/workflows/verify.yml)
  rebuilds every module from source and runs the combined [certificate](../../Certificate.lean), which
  includes these three theorems.

To reproduce from the public repository:

```sh
lake exe cache get
lake build SmallGammaGeodesics.Frozen.DeviationScale SmallGammaGeodesics.Frozen.FunctionalTightness \
  SmallGammaGeodesics.Frozen.GeodesicAeUnique
lake env lean results/small-parameter-lqg-geodesics/Check.lean
for m in DeviationScale FunctionalTightness GeodesicAeUnique; do
  lake env leanchecker --fresh SmallGammaGeodesics.Frozen.$m
done
```

`Check.lean` runs `#print axioms` on each theorem; the expected output is `[propext, Classical.choice,
Quot.sound]`. `leanchecker --fresh` accepts a single module, hence the loop; each run replays Mathlib as
well.

The sources are published byte-for-byte. Their docstrings cite development documents that are not part of
this snapshot: the corrected rewrite ("blueprint"), rulings (such as G12 above), audits, work packets and
the frozen-anchor manifest. They also mention `CC/LusinCounterexample.lean` and `Probes/Erratum.lean`,
development files that record counterexamples to superseded intermediate statements; the theorems do not
use them, and they are not part of this snapshot. Kernel checking establishes the Lean proofs;
correspondence with the paper is the subject of the conventions above.

## Credits

The paper builds on Ding–Gwynne [1] (arXiv:1807.01072), Gwynne–Miller [2]–[4] (arXiv:1905.00383,
1905.00384, 1905.00381) and Kavvadias [5] (arXiv:2509.15544). The formalization reuses the [LQG
metric](../lqg-metric/), [Gaussian LQG distance](../gaussian-lqg-distance/), [small-parameter LQG
dimension](../small-gamma-dimension/) and [Quantum Zipper](../quantum-zipper/) releases, which also
formalize results of Ding–Dubédat–Dunlap–Falconet, Dubédat–Falconet–Gwynne–Pfeffer–Sun,
Ding–Zeitouni–Zhang and Miller–Qian. The original mathematical results are due to their authors;
source-file attribution is retained. The statements were frozen and audited following Scott Armstrong's
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) workflow.

[All released formalizations](../../README.md)
