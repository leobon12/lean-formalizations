# Almost sure continuity of the higher-dimensional LQG metric

Lean formalization of **Theorem 1.1** of *Almost sure continuity of the higher-dimensional LQG metric*
(October 2026; 34 pages; AI research paper, not public; SHA-256
`05368f93753972dd5e6965d78058269ccb9805c8bb9ea2b6af8d670b9f2e5934`, AI-generated and unrefereed),
developed under Leonardo Bonanno's direction with AI assistance. The paper presents a research proof that
takes the uniqueness and strong characterization of higher-dimensional exponential metrics from a
supplied manuscript [8] as a standing input, and uses two further supplied manuscripts and five published
works. Every step of the paper, and of the results it imports, was audited before the statements were
frozen; the corrections are listed below.

The formalization covers **Theorem 1.1 in every dimension d ≥ 3, with no assumptions**. Normalize the
γ-LQG metric of the whole-space log-correlated Gaussian field on ℝ^d (0 < γ < √(2d)) so that the median
of its distance from 0 to e₁ is one, and take the Euclidean metric at γ = 0. These metrics admit versions
on the same field such that, almost surely, γ ↦ D^γ_h is continuous on [0, √(2d)) for locally uniform
convergence of distances; on the same event, every D^γ_h is a continuous length metric inducing the
Euclidean topology. The paper's standing input [8] is not assumed: its theorems are proved with no
assumptions in the [higher-dimensional exponential metrics release](../higher-dimensional-lqg-metric/) of
this repository, which this formalization imports. The paper's other inputs are proved here or replaced:
the estimates of Ding–Gwynne–Zhuang [1] uniformly in the parameter, the parametrization γ ↔ ξ (in place
of [3]), the small-parameter estimates of the unavailable manuscript [9] (by a new proof of the paper's
Lemma 5.1), and Alexander duality [6] (by a quantitative nonseparation lemma in d ≥ 3).

[Theorem 1.1](../../HigherDimLQGContinuity/Frozen/Theorem11Metric.lean#L51-L66) · [Frozen
statements](../../HigherDimLQGContinuity/Frozen/) · [Proofs](../../HigherDimLQGContinuity/Assembly/) ·
[Final assembly](../../HigherDimLQGContinuity/Final/) · [Focused certificate](Check.lean) · [Verification
record](verification.json)

## The theorem

Fix d ≥ 3. The field h is the whole-space log-correlated Gaussian field (LGF) on ℝ^d normalized by
h_1(0) = 0: a random distribution whose pairings with mean-zero test functions are centred Gaussian with
covariance ∬ φ(x) log(1/‖x − y‖) ψ(y) dx dy, and whose average over the unit sphere vanishes. Its law
exists and is unique. For ξ > 0, Q(ξ) is the distance exponent of Liouville first passage percolation;
the subcritical range is Q(ξ) > √(2d). A metric assignment h ↦ D_h is *strong at (ξ, Q)* if, whenever
the input is an LGF plus a random continuous function, D_h is a length metric inducing the Euclidean
topology, its internal metrics on open sets are local functions of the field, D_{h+f} = e^{ξf}·D_h for
all continuous f at once (Weyl scaling), and D_h(ru + z, rv + z) = D_{h(r·+z)+Q log r}(u, v) (coordinate
change). By [8], for subcritical ξ such an assignment exists at Q = Q(ξ) and is unique up to a
deterministic positive constant. For 0 < γ < √(2d), the γ-LQG metric is this assignment at the Weyl
parameter ξ with Q(ξ) = d/γ + γ/2.

**Theorem 1.1.** Normalize the γ-LQG metric by med D^γ_h(0, e₁) = 1 for 0 < γ < √(2d), and set D^0_h(x,
y) = |x − y|. The metrics admit versions on the same field such that, almost surely, γ ↦ D^γ_h is
continuous on [0, √(2d)) for locally uniform convergence of distances. Thus, on one event of probability
one, for every γ₀ ∈ [0, √(2d)) and every R < ∞, the supremum of |D^γ_h(x, y) − D^{γ₀}_h(x, y)| over x, y
in the ball of radius R tends to 0 as γ → γ₀.

The proof declaration is `HigherDimLQGContinuity.theorem11_metric`. Its statement, copied from
[`HigherDimLQGContinuity/Frozen/Theorem11Metric.lean`](../../HigherDimLQGContinuity/Frozen/Theorem11Metric.lean#L51-L66)
(inside `namespace HigherDimLQGContinuity`, with `open MeasureTheory Filter Topology Set`, `open
HigherDimLQGMetric` and `open HigherDimLFPP (Rd)`), is:

```lean
theorem theorem11_metric :
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
```

Its proof is `by exact HigherDimLQGContinuity.theorem11_metric_impl`
([`Assembly/Theorem11Metric.lean`](../../HigherDimLQGContinuity/Assembly/Theorem11Metric.lean)). In
words: for every d ≥ 3 there is one map D(γ, g), jointly measurable in the parameter γ ∈ ℝ and the
distribution g, with values in the continuous functions on ℝ^d × ℝ^d, such that

- **(Euclidean endpoint)** D(0, g) is the Euclidean distance |x − y|, for every g;
- **(versions)** for every γ ∈ (0, √(2d)), every ξ > 0 with Q(ξ) = d/γ + γ/2, every assignment E that is
  strong at (ξ, Q(ξ)) and has median one, and every normalized LGF h on any probability space, D(γ, h) =
  E_h almost surely;
- **(continuity and metrics)** for every normalized LGF h on any probability space, almost surely: for
  every γ₀ ∈ [0, √(2d)) and every R > 0, the supremum of |D(γ, h)(x, y) − D(γ₀, h)(x, y)| over x, y in
  the closed ball of radius R tends to 0 as γ → γ₀ within [0, √(2d)); and every D(γ, h), γ ∈ [0, √(2d)),
  is the distance function of a continuous length metric on ℝ^d that induces the Euclidean topology.

The null set of the version clause may depend on γ, E and h, as for any version; the continuity and the
metric property hold on one event for all parameters at once. Median-one strong assignments exist
(`medianOneStrong_exists` below), and two of them at the same ξ agree almost surely: by [8] they differ
by a deterministic constant, and the median of D_h(0, e₁) is unique. So the version clause is about *the*
γ-LQG metric of the paper. The clause quantifies over every ξ with Q(ξ) = d/γ + γ/2, so nothing is
chosen; `prop18` shows that there is exactly one such ξ.

### The other frozen theorems

Four further theorems were frozen with the main one. `theorem11` is the paper's statement without the
metric property (the γ-form), `theorem11Xi` the same statement in the Weyl parameter ξ; `prop18` is the
parametrization γ ↔ ξ that the paper takes from [3]; `medianOneStrong_exists` shows that the version
clauses are not vacuous. Their statements, from
[`HigherDimLQGContinuity/Frozen/`](../../HigherDimLQGContinuity/Frozen/), are:

```lean
-- Theorem 1.1 in γ, without the metric property
theorem theorem11 :
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

-- Theorem 1.1 in the Weyl parameter ξ, on xiRange d = {0} ∪ {ξ > 0 : √(2d) < Q(ξ)}
theorem theorem11Xi :
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

-- the parametrization (1.5): Q is continuous on (0, ∞) and strictly decreasing on the subcritical range,
-- ξ Q(ξ) → 1,
-- and γ ↦ ξ is an increasing homeomorphism Ξ of [0, √(2d)) onto xiRange d with Q(Ξ γ) = d/γ + γ/2 and
-- γ/Ξ γ → d
theorem prop18 :
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

-- non-vacuity: median-one strong assignments exist at every subcritical ξ
theorem medianOneStrong_exists :
    ∀ d : ℕ, 3 ≤ d → ∀ ξ : ℝ, 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ E : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) E ∧ IsMedianOne d E :=
```

Line-anchored sources: [`theorem11`](../../HigherDimLQGContinuity/Frozen/Theorem11.lean#L50-L64),
[`theorem11Xi`](../../HigherDimLQGContinuity/Frozen/Theorem11Xi.lean#L49-L61) (both with the opens of the
main theorem), [`prop18`](../../HigherDimLQGContinuity/Frozen/Prop18.lean#L45-L56) (with `open Filter
Topology Set` and `open HigherDimLQGMetric`) and
[`medianOneStrong_exists`](../../HigherDimLQGContinuity/Frozen/MedianOneStrongExists.lean#L38-L40) (with
`open HigherDimLQGMetric`).

[`Check.lean`](Check.lean) restates all five statements verbatim and checks that the frozen declarations
prove them. It then derives, in dimension three at γ = 1, a subcritical parameter ξ with Q(ξ) = 3/1 +
1/2, a median-one strong assignment E at ξ and the normalized field, and shows that the family of
`theorem11_metric` agrees with E at γ = 1 almost surely under the law of the normalized field and
consists of length metrics. So the hypotheses of the version clause can be met, and the theorem says
something about the γ-LQG metric.

## The frozen definitions

The four definitions of this formalization are frozen in their own files under
[`HigherDimLQGContinuity/Frozen/`](../../HigherDimLQGContinuity/Frozen/); the objects of [8] are the
frozen definitions of the [previous release](../higher-dimensional-lqg-metric/), imported unchanged.

| Paper | Lean | Definition |
| --- | --- | --- |
| D^0_h(x, y) = \|x − y\| | [`euclidDistC d`](../../HigherDimLQGContinuity/Frozen/EuclidDistC.lean#L25) | The Euclidean distance of ℝ^d as a point of C(ℝ^d × ℝ^d, ℝ), the codomain of the family. |
| med D^γ_h(0, e₁) = 1 | [`IsMedianOne d E`](../../HigherDimLQGContinuity/Frozen/IsMedianOne.lean#L37) | 1 is a median of E_h(0, e₁) when h has the law `normLGFLaw d` of the normalized LGF: both {E_h(0, e₁) ≤ 1} and {E_h(0, e₁) ≥ 1} have probability at least 1/2. The sets are measured by the outer measure, which agrees with the measure for every measurable E, so there is no junk law for a non-measurable E. |
| sup over x, y ∈ B_R of the distance difference | [`supDistLU d R F G`](../../HigherDimLQGContinuity/Frozen/SupDistLU.lean#L31) | The supremum of \|F(x, y) − G(x, y)\| over the closed ball of radius R, in [0, ∞]. |
| [0, ξ_c) | [`xiRange d`](../../HigherDimLQGContinuity/Frozen/XiRange.lean#L29) | {0} ∪ {ξ > 0 : √(2d) < Q(ξ)}, defined without a supremum; by `prop18` it is the image of [0, √(2d)) under the parametrization. |
| ℝ^d, e₁, distributions | [`Rd d`](../../HigherDimLFPP/Frozen/Rd.lean#L20), [`e₁ d`](../../HigherDimLFPP/Frozen/E1.lean#L19), [`DistRd d`](../../HigherDimLQGMetric/Frozen/DistRd.lean#L24) | `EuclideanSpace ℝ (Fin d)`, its first unit vector, and the distributions on ℝ^d with the σ-algebra generated by the pairings. |
| the normalized LGF | [`IsNormalizedLGF h P`](../../HigherDimLQGMetric/Frozen/IsNormalizedLGF.lean#L26), [`normLGFLaw d`](../../HigherDimLQGMetric/Frozen/NormLGFLaw.lean#L29) | A whole-space LGF with h_1(0) = 0 almost surely, and its law, which exists and is unique (`normLGFLaw_spec` of the previous release). |
| Q(ξ) | [`distExp d ξ`](../../HigherDimLQGMetric/Frozen/DistExp.lean#L28) | The kernel-independent distance exponent of LFPP (`distExp_spec` of the previous release). |
| metrics | [`ContMetric d`](../../HigherDimLQGMetric/Frozen/ContMetric.lean#L26), [`.IsLength`](../../HigherDimLQGMetric/Frozen/ContMetricIsLength.lean#L25) | Continuous metrics on ℝ^d inducing the Euclidean topology, as a subspace of C(ℝ^d × ℝ^d, ℝ); the length-space property. |
| the γ-LQG metric (strong axioms) | [`IsStrongExpMetric d ξ Q D`](../../HigherDimLQGMetric/Frozen/IsStrongExpMetric.lean#L41) | Definition 1.1 of [8]: measurability and the four axioms (length metric, locality, Weyl scaling, coordinate change), each required for every LGF plus a continuous function on every probability space. |

## Correspondence with Theorem 1.1

- **Versions on the same field** are one map D, jointly measurable in (γ, g), evaluated at the given
  field. The paper constructs a field-measurable family (§5); joint measurability is a stronger reading
  (ruling N4).
- **(1.2)** is `IsMedianOne` under the law of the field normalized by h_1(0) = 0. The pin matters,
  because D_{h+c} = e^{ξc}·D_h.
- **(1.3) and (1.4)**: the continuity clause is the explicit form (1.4), with closed balls; for
  continuous functions the two readings agree.
- **The parameter.** The paper writes D^γ for the γ-LQG metric and proves the theorem in the Weyl
  parameter ξ, through Q(ξ) = d/γ + γ/2. `theorem11_metric` is stated in γ, and its version clause
  quantifies over every ξ that solves this equation; `prop18` shows that the solution is unique and that
  γ ↦ ξ is an increasing homeomorphism of [0, √(2d)) onto `xiRange d`.
- **Genuine metrics.** The paper proves in §§5.3–5.4 that every member of the family is a metric on one
  event. The last clause of `theorem11_metric` says that, on the event of the continuity clause, every
  D(γ, h) is a continuous length metric inducing the Euclidean topology (ruling N11). `theorem11` is the
  same statement without this clause.

## Scope and statement conventions

- **Probability spaces** range over Lean's `Type` universe; this is equivalent to the canonical form.
- **Joint measurability** of the family strengthens the paper's field-measurable family (ruling N4).
- **The parametrization.** `prop18` asserts more than the paper: continuity of Q on (0, ∞), strict
  decrease on the subcritical range and ξQ(ξ) → 1 as ξ ↓ 0. Its proof does not use [3] (see the inputs
  below). The finiteness of ξ_c is proved in the library (`xiCrit_le`: ξ_c ≤ √(2d) − √(2d − 2)) but is
  not part of the frozen statement; the paper does not need it.
- **The version clause** ranges over the median-one strong assignments, the γ-LQG metrics of [8].
  Assignments of [8]'s weak class are covered by [8]'s Theorem 1.4 with the uniqueness of the median, but
  are not stated.
- **Metrics, properness, geodesics.** `theorem11_metric` asserts, on one event of probability one, that
  every member D(γ, h), γ ∈ [0, √(2d)), is a continuous metric inducing the Euclidean topology with the
  length property. The paper also proves properness and geodesics at every parameter; the library proves
  them too for the positive parameters
  ([`ae_metric_proper_version`](../../HigherDimLQGContinuity/MetricVersion/Main.lean#L45),
  [`ae_isLength_version`](../../HigherDimLQGContinuity/MetricVersion/Main.lean#L97)), but they are not
  part of the frozen statement.
- **Non-vacuity.** Without `medianOneStrong_exists`, the family D(γ, g) := |x − y| would satisfy the
  version clause vacuously. The statement audit therefore required that the main theorems count as proved
  only once `prop18` and `medianOneStrong_exists` are sealed; both are.
- **Junk values.** Lean's definitions are total. `IsMedianOne` is stated with sets under `normLGFLaw d`,
  so it has no push-forward junk; `supDistLU` is a supremum in [0, ∞], and `xiRange` is defined without a
  supremum; `distExp` and `normLGFLaw` are chosen when they exist (junk 0 otherwise), and the sealed
  `distExp_spec` and `normLGFLaw_spec` of the previous release show that they exist and are unique. The
  independent statement audit traced every construct that can take a junk value and found each
  unreachable or excluded.
- **Dimension.** The theorems are stated for d ≥ 3, as in the paper; several intermediate results are
  proved for d ≥ 2.

## No assumptions: the inputs

The paper cites ten works. Each is a theorem here or in the previous release, or is not needed:

| Paper's input | What the paper uses | In this release |
| --- | --- | --- |
| [8] *Higher-dimensional exponential metrics: a proposed axiomatic existence and uniqueness proof* (supplied manuscript) | Theorems 1.2 and 1.4, Corollaries 10.2 and 10.4, Lemma 10.3: the strong characterization, existence and uniqueness of the γ-LQG metric, LFPP limits, the median | **proved** in the [previous release](../higher-dimensional-lqg-metric/), with no assumptions; used here through its theorems [`theorem12`](../../HigherDimLQGMetric/Frozen/Theorem12.lean#L42) and [`strongUniqueness`](../../HigherDimLQGMetric/Frozen/StrongUniqueness.lean#L34) and its §10 lemmas (`lemma101`, `lemma103_median_unique`, `l10a_subseq_limit_median_one`). The paper cites a revised version of [8]; the planning audit found that the cited statements are unchanged. |
| [1] Ding–Gwynne–Zhuang | the tightness and comparison estimates of LFPP, uniformly in the parameter (Appendix A) | **proved** (block D1): the fixed-ξ port of [1] in the previous release is made uniform in ξ over compact parts of the subcritical range, with [1]'s unproved d-dimensional duality steps repaired |
| [2] Contreras Hip–Zhuang, Proposition 1.10 | the law identity of the convolution field (Appendix A) | **proved** in the previous release (`l1e_law`) |
| [3] Contreras Hip–Zhuang, Proposition 1.8 and Corollary 1.9 | the parametrization γ ↔ ξ | **replaced**: [3] concerns a different exponent; the parametrization follows from a new bound, ξQ(ξ) is √(2d)-Lipschitz with value 1 at 0 ([`phiXi_lipschitz`](../../HigherDimLQGContinuity/Param/Lipschitz.lean#L261), [`prop18_holds`](../../HigherDimLQGContinuity/Param/Prop18.lean#L158)) |
| [5] Chen–Dafnis–Paouris, Theorem 1(i) | the Gaussian product inequality behind (2.9) | **proved** in the previous release (`gaussianHolder_prob`), used through its shell decoupling |
| [6] Hatcher, Alexander duality | Lemma 4.1: clearance around an arc | **replaced** in d ≥ 3 by Lemma 4.1′, a bisection on the nonseparation theorems of the previous release ([`lemma41_clearance`](../../HigherDimLQGContinuity/Topology/Clearance.lean#L371)) |
| [9] *First-order fluctuations of small-parameter exponential metrics* (supplied manuscript) | Lemma 5.1, the small-parameter estimates at the Euclidean endpoint | **replaced** by a new proof of Lemma 5.1 ([`marginalEuclid_of`](../../HigherDimLQGContinuity/MarginalEuclid/Main.lean#L18)): a pairing frame of the field, a Gaussian L^p inequality, rotation invariance in law through LFPP, and Kolmogorov chaining. [9] is not available and assumes rotation covariance, which is not an axiom of [8]. |
| [4] Ding–Gwynne, [7] Kavvadias, [10] (supplied manuscript) | the strategy of §4's field-modification count; the planar analogue and the median convention; an almost sure LFPP theorem at fixed parameter, which the paper does not use | **not needed** |

## How the proof is organized

The rewrite of the paper has four parts: A, the paper's §§1–3; B, §4; C, §5; D, Appendix A. Each part was
formalized as a set of work packets that met through frozen interface statements, so that the parts could
be proved in parallel; the assembly then discharges every interface.

| Block | Paper | Directories | Main results | Lines |
| --- | --- | --- | --- | ---: |
| A1 the parametrization | §1, (1.5) | `Param/`, `Median/`, `Windows/` | `phiXi_lipschitz`, `prop18_holds`, [`medianOneStrong_holds`](../../HigherDimLQGContinuity/Median/MedianOneStrong.lean#L53), [`subcritLocal_holds`](../../HigherDimLQGContinuity/Windows/Basic.lean#L33) | 1,267 |
| A2 estimates | §2: pins and exact scaling, Lemmas 2.2–2.4, the events H↓ and H↑ | `Norm/`, `Caps/`, `Witness/`, `Events/` | [`rho_scaling`](../../HigherDimLQGContinuity/Norm/Scaling.lean#L96), [`lemma22`](../../HigherDimLQGContinuity/Caps/Lemma22.lean#L117), [`cover210_full`](../../HigherDimLQGContinuity/Caps/CoverFull.lean#L63), [`isWitness_iff`](../../HigherDimLQGContinuity/Witness/Basic.lean#L249), [`local_events_aeEventIn`](../../HigherDimLQGContinuity/Events/Local.lean#L156), [`connector_of_good`](../../HigherDimLQGContinuity/Events/Connector.lean#L252) | 4,843 |
| A3 comparison by local improvement | §3: sewing (Lemma 3.1), Lemmas 3.2 and 3.4, Propositions 3.3, 3.6 and 3.7 | `Sewing/`, `Amplify/`, `Favorable/`, `Seed/` | [`lemma31a`](../../HigherDimLQGContinuity/Sewing/Lemma31a.lean#L129), [`lemma31b`](../../HigherDimLQGContinuity/Sewing/Lemma31b.lean#L663), [`lemma32`](../../HigherDimLQGContinuity/Amplify/Lemma32.lean#L119), [`prop33`](../../HigherDimLQGContinuity/Amplify/Prop33.lean#L48), [`lemma34`](../../HigherDimLQGContinuity/Favorable/Lemma34.lean#L88), [`prop36`](../../HigherDimLQGContinuity/Seed/Prop36.lean#L137), [`prop37`](../../HigherDimLQGContinuity/Seed/Prop37.lean#L78) | 7,114 |
| B1 routing and labels | §4.1: Lemma 4.1′, favorable arcs and leads, site geometry, labels, the plateau network, the catalogue | `Topology/`, `Routing/`, `Labels/`, `Network/`, `LabelEvents/` | `lemma41_clearance`, [`exists_leads`](../../HigherDimLQGContinuity/Routing/Leads.lean#L553), [`rational_general_position`](../../HigherDimLQGContinuity/Routing/GeneralPosition.lean#L465), [`gate_sandwich`](../../HigherDimLQGContinuity/Labels/Cells.lean#L108), [`siteConsts_spec`](../../HigherDimLQGContinuity/Labels/OrderSpec.lean#L63), [`labelNet_spec`](../../HigherDimLQGContinuity/Network/SpecFinal.lean#L187), [`labelCatalogue_card_le`](../../HigherDimLQGContinuity/Network/Catalogue.lean#L90), [`exists_label_of_seedFav`](../../HigherDimLQGContinuity/LabelEvents/LabelExists.lean#L271) | 16,652 |
| B2 the local certificate | §4.2: Weyl modifications, Lemma 4.3, the bump energy, the site certificate, chronological restoration | `Forcing/`, `SiteCert/`, `Restore/` | [`lemma43_forcing_holds`](../../HigherDimLQGContinuity/Forcing/Forcing.lean#L18), [`bump_energy`](../../HigherDimLQGContinuity/SiteCert/Bump.lean#L373), [`chronological_restoration`](../../HigherDimLQGContinuity/Restore/Geometry.lean#L148), [`siteCert_holds`](../../HigherDimLQGContinuity/SiteCert/Holds.lean#L21) | 4,778 |
| B3 the forcing count and Proposition 3.5 | §§4.3–4.4: Lemma 4.4, Proposition 4.5, the site event, the proof of Proposition 3.5 | `Overlap/`, `ForcingCount/`, `SiteEvents/`, `Improve/` | [`lemma44_pinned_holds`](../../HigherDimLQGContinuity/Overlap/Holder.lean#L252), [`siteEvent_prob`](../../HigherDimLQGContinuity/SiteEvents/SiteProb.lean#L142), [`prop45`](../../HigherDimLQGContinuity/ForcingCount/Prop45.lean#L393), [`prop35_of`](../../HigherDimLQGContinuity/Improve/Prop35.lean#L45) | 11,873 |
| C1 positive parameters | §5.1: grids, interpolation, gluing of parameter windows | `Grid/`, `Version/` | [`windowVersion_spec`](../../HigherDimLQGContinuity/Grid/Version.lean#L167), [`posVersion_of`](../../HigherDimLQGContinuity/Version/Glue.lean#L247) | 2,350 |
| C2 Lemma 5.1 and the Euclidean endpoint | §5.2: pairing frame, rotation invariance in law, concentration, Hölder moments, Lemma 5.1, (5.5)–(5.8) | `Rotation/`, `Frame/`, `Concentration/`, `MarginalEuclid/`, `Endpoint/` | [`strongRotLaw_holds`](../../HigherDimLQGContinuity/Rotation/Law.lean#L37), [`exists_pairingFrame`](../../HigherDimLQGContinuity/Frame/Exists.lean#L71), [`concentration_of`](../../HigherDimLQGContinuity/Concentration/Main.lean#L313), `marginalEuclid_of`, [`endpoint_of`](../../HigherDimLQGContinuity/Endpoint/Main.lean#L283) | 9,676 |
| C3 medians, Theorem 1.1 and metrics | §§5.3–5.4: medians, the final version, the metric-valued strengthening | `Final/`, `MetricVersion/` | [`theorem11Xi_of_parts`](../../HigherDimLQGContinuity/Final/Xi.lean#L194), [`theorem11_of`](../../HigherDimLQGContinuity/Final/Gamma.lean#L38), [`theorem11_metric_of_parts`](../../HigherDimLQGContinuity/Final/Metric.lean#L157), [`metricVersion_of`](../../HigherDimLQGContinuity/MetricVersion/Main.lean#L112) | 2,423 |
| D1 uniform estimates of [1] | Appendix A.1: [1] §§4–6 uniformly in ξ, Proposition A.1 | `UnifBase/`, `Unif4/`, `Unif5/`, `UnifCompare/`, `UnifTight/`, `UnifNondeg/` | [`uExpRate`](../../HigherDimLQGContinuity/UnifBase/ExpRate.lean#L282), [`uCor52`](../../HigherDimLQGContinuity/UnifCompare/Cor52.lean#L42), [`uDistInf`](../../HigherDimLQGContinuity/UnifTight/DistInf.lean#L485), [`uNondeg`](../../HigherDimLQGContinuity/UnifNondeg/Main.lean#L82), [`uQuantComp`](../../HigherDimLQGContinuity/UnifNondeg/Main.lean#L87) | 9,665 |
| D2 moments and escape | Appendix A.2: moments at the cutoff, transfer to the convolution LFPP, passage to the continuum, continuum estimates, Theorem A.3 | `Crude/`, `MomentsW1/`, `MomentsW2/`, `ConvTransfer/`, `Fatou/`, `Continuum/`, `Lemma21/` | [`wnUpperMoment`](../../HigherDimLQGContinuity/MomentsW1/UpperMoment.lean#L16), [`wnInvCross`](../../HigherDimLQGContinuity/MomentsW2/Main.lean#L61), [`convUpperMoment`](../../HigherDimLQGContinuity/ConvTransfer/UpperFinal.lean#L23), [`continuum_fatou`](../../HigherDimLQGContinuity/Fatou/Main.lean#L17), [`continuum_escape`](../../HigherDimLQGContinuity/Continuum/Escape.lean#L513), [`lemma21_of`](../../HigherDimLQGContinuity/Lemma21/A3.lean#L184) | 16,071 |
| E assembly | the statement surface, the interfaces and their discharge, the providers | `Core/`, `Discharge/`, `Assembly/`, `Frozen/` | [`uniformEstimates_holds`](../../HigherDimLQGContinuity/Discharge/Estimates.lean#L50) (Lemma 2.1), [`marginalEuclid_holds`](../../HigherDimLQGContinuity/Discharge/Estimates.lean#L63) (Lemma 5.1), [`theorem11Metric_of_siteCert`](../../HigherDimLQGContinuity/Discharge/Theorem11.lean#L61), [`theorem11_metric_impl`](../../HigherDimLQGContinuity/Assembly/Theorem11Metric.lean#L25) | 1,698 |
| | | | **Total** | **88,410** |

The assembly follows the paper. Theorem 1.1 is `theorem11_metric_of_parts` applied to the
positive-parameter family (`posVersion_of`, from Proposition 3.7), the Euclidean endpoint (`endpoint_of`,
from Proposition 3.7 and Lemma 5.1), the metric-valued strengthening (`metricVersion_of`, with the
pairing frame) and the parametrization (`prop18_holds`). Proposition 3.7 follows from Lemma 2.1
(`uniformEstimates_holds`, through Appendix A) and Proposition 3.5 (`prop35_of`, with the site
certificate `siteCert_holds` of §4.2), whose proof is the paper's §4. The paper's §3 turns local
improvements into a comparison at fixed confidence; §5 builds the family on compact parameter windows and
at the Euclidean endpoint, and returns from the mean-log normalization to the median normalization.

## Differences from the paper

### Corrected statements

The proof follows a corrected rewrite of the paper and of its inputs ("blueprint", 133 pages), prepared
from independent section-by-section audits; its errata list has 112 items (26 for §§1–3, 29 for §4, 18
for §5 and 39 for Appendix A). While writing the proofs, the formalization found that several
intermediate statements of the rewrite, of the audits or of the work packets were false as written. Each
was corrected by a recorded ruling, numbered as in the development records that many source docstrings
cite; none of them changed a frozen statement:

| Ruling | Statement | What was wrong | Correction |
| --- | --- | --- | --- |
| N17 | the interval covers behind Lemma 3.1 (sewing), as first written in the rewrite | the ends of a minimal cover need not increase strictly: J₁ = [0, 2/5), J₂ = (0, 4/5), J₃ = (3/5, 1] is a minimal cover of [0, 1] with inf J₁ = inf J₂ | nondecreasing ends, and the interior members lie in [s, t] without containing s or t ([`interval_cover`](../../HigherDimLQGContinuity/Sewing/Intervals.lean#L342)); Lemma 3.1 is unchanged |
| N18 | the characterization of witnesses in §2, "for every continuous metric" | false when the internal distance between the endpoints is infinite | stated for length metrics, which is every use (`isWitness_iff`) |
| N19 | chronological restoration (consequences of Lemma 4.3), in the planning audit's form | a negative cost of an unvisited collector can cancel a needed positive cost | the costs are nonnegative, as in the rewrite (`chronological_restoration`) |
| N20 | the site certificate of §4.2, clause (iv), in the rewrite | false for primary metrics that are not length metrics: min(D, c) keeps every internal metric but breaks the global bound | assumes a length metric, which every use has |
| N21 | the scale factor S_ξ(r, z) at ξ = 0, as first implemented | built from ξQ(ξ) it gives S_0 = 1 instead of the Euclidean value r, so Lemma 2.2(b) fails at ξ = 0 | built from ϕ(ξ), which is 1 at ξ = 0; the scaling identities are stated for ξ > 0 |
| N22 | the covering (2.10), as first implemented | it required events local in ann(0, 1/2, s + 1), which at pin 1 misses part of the annulus on which the local references depend, so it could not be applied to them | events local in ann(0, 1/2, max(7/2, s + 1)) (`cover210_full`) |
| N29 | the exponents of the site constants in §4.1, in the rewrite | a minimum of three powers of v is not comparable to its first term in general (explicit counterexamples in d = 3) | corrected exponents (maxima of the three); the polynomial bounds used downstream are unchanged |
| N30 | rational general position in §4.1, in the planning audit's form with ordered edges | with both (0, 1) and (1, 0) as edges the incidence clause forces w₀ = w₁ (formal counterexample) | unordered edges, as in the rewrite (`rational_general_position`) |

Further corrections of the same kind are recorded only in the blueprint errata, for example: in the
uniform Lemma 5.9 of [1] the constant depends on the truncation level K, as in the fixed-ξ form; the
arithmetic shortcut (4s)^σ ≤ 4s, false for 0 < σ < 1, is replaced in the site units. One interface pair
of Appendix A was circular (the uniform Hölder tightness was normalized by a median whose control was to
be derived from it); the cycle was broken by proving the comparability from high-quantile forms (ruling
N28).

### Gaps repaired

The audits found no false step in the paper's own argument; its gaps were repaired with full proofs. The
serious ones concern the inputs:

- **[3] for the parametrization.** [3] proves the parametrization for its own exponent (set-to-set
  crossings of box-averaged lattice LFPP), which is not known to equal the point-to-point exponent of
  [8]. The formalization proves that ϕ(ξ) = ξQ(ξ) is √(2d)-Lipschitz on [0, ∞) with ϕ(0) = 1, and derives
  the parametrization from it. A Markov bound ϕ(ξ) ≤ 1 + ξ²/2 gives ξ_c ≤ √(2d) − √(2d − 2), and the
  interval property of the subcritical range, used but not proved in the paper, is proved.
- **[9] for Lemma 5.1.** [9] is not available, and its argument assumes rotation covariance, which is not
  an axiom of [8], and an infinite-dimensional log-Sobolev bootstrap. Lemma 5.1 is proved directly, and
  the paper's Corollary A.4 and the small-parameter clause of Lemma 2.1 are not needed.
- **[1] in Appendix A.** [1] uses a d-dimensional duality at several places without proof, and its
  clipped-diameter and "around" bounds are not proved there. Both are repaired with the deterministic
  lemmas of the repository. The estimates are made uniform in the parameter, and Lemma 2.1 holds
  uniformly down to ξ = 0.
- **[6] for Lemma 4.1.** Alexander duality is replaced in d ≥ 3 by a quantitative nonseparation argument
  (Lemma 4.1′) with an explicit clearance, and the order of constants on p. 14 is adjusted accordingly.
- **Quantifiers and constants.** The order of constants of Propositions 3.3 and 3.5, the domains and pins
  of the local events, and the measurability of the events of §4 are made explicit (Borel representatives
  that agree almost surely).

### Not formalized

- Properness and geodesics of every member of the family as part of the frozen statement (see the
  conventions above).
- Weak assignments of [8] in the version clause, and the finiteness of ξ_c in the frozen statement.
- The paper's Corollary A.4 and the small-parameter clause of Lemma 2.1, which the new proof of Lemma 5.1
  does not need.
- Numerical values of the constants.

## How the statements are pinned

- **Frozen statement surface.** The 9 statements (4 definitions and 5 theorems) were written one
  declaration per file before any proof, and audited independently against the paper: each theorem type
  was reconstructed from the paper and found equivalent to the frozen one, with no hypothesis beyond the
  paper's. `theorem11_metric` was added after the first audit found that the metric property of the
  family was not frozen; a second audit approved it. A manifest records, for every declaration, a hash of
  its elaborated type and definition body and a hash of its file, and a guard checks the files against
  it, accepting no change but the one-line proof bodies; a fingerprint covers the 139 non-Mathlib
  constants that the statements reach, and the 49 upstream files they use are pinned by hash. At every
  seal these were recomputed and found unchanged. The SHA-256 of every frozen file is recorded in
  [verification.json](verification.json).
- **Two-key seals.** Each theorem was sealed twice: first by mechanical checks (only the proof body
  changed, the manifest guard passes, the statement hashes are identical, the build is fresh, the axioms
  are standard), then by an independent audit, run by a different agent than the one that wrote the
  proof, which also reviewed the proof route for hypothesis smuggling and junk values. Seals: All five
  frozen theorems are sealed with two keys: seal batch 1 (`medianOneStrong_exists`, `prop18`; independent
  audit A-seal-1 PASS) and seal batch 2 (`theorem11Xi`, `theorem11`, `theorem11_metric`; independent
  audit A-seal-2 PASS). Key 1 is the frozen-anchor guard on a clean export, the unchanged ABI and
  statement-closure fingerprint, and `#print axioms` (standard axioms only); key 2 is an independent seal
  audit with a kernel replay..
- **Axioms.** `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for each of the five
  theorems, and the certificates below traverse every declaration of the included libraries. No `sorry`,
  `admit`, custom `axiom` or unsafe declaration occurs in the shipped sources (checked by the public
  source scan), and the axiom audits would reject `native_decide`, whose proofs depend on an extra axiom.
- **Kernel replay.** `leanchecker --fresh` re-checked every declaration of the closure, Mathlib included,
  in a fresh environment (exit code 0 on 22 October 2026, 11:24–11:33 CEST, in 8 min 34 s, on the Lean
  sources of commit `e673af9df`).

## Dependencies

The library reuses earlier releases of this repository; none of their released modules changes. The
export also adds `HigherDimLQGMetric/Sec4/Bridge.lean`, a module of an earlier library that its own
release did not need; the released modules of that library are unchanged.

| Library | Modules in the closure | What this release uses |
| --- | ---: | --- |
| HigherDimLQGContinuity (new) | 454 | this formalization |
| [HigherDimLQGMetric](../higher-dimensional-lqg-metric/) | 1,300 | the paper's standing input [8]: the strong exponential metrics, their existence, uniqueness and LFPP limits, the median, properness and geodesics; the fixed-ξ port of [1] that Appendix A makes uniform; nonseparation, Gaussian Hölder and shell decoupling |
| [HigherDimLFPP](../higher-dim-lfpp/) | 97 | ℝ^d, e₁, white noise and band fields, admissible kernels, LFPP distances and exponents |
| [LQGMetric](../lqg-metric/) | 667 | metric geometry (internal metrics, length spaces, geodesics, midpoints), measurability tools, and tail and moment estimates from the planar LQG metric papers |
| [QuantumZipper](../quantum-zipper/) | 734 | the Cameron–Martin zero–one law, Kolmogorov continuity, Cameron–Martin shifts and laws of Gaussian vectors |
| [LQGDimension](../small-gamma-dimension/) | 38 | Gaussian lemmas, directly and through the earlier releases |
| [GaussianLQG](../gaussian-lqg-distance/) | 49 | Gaussian moments and the Gaussian L^p inequality, medians and their limits, and the planar estimates at the Euclidean endpoint that the proof of Lemma 5.1 ports |

Lean is `v4.34.0-rc2` and Mathlib is `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`, as for the rest of the
repository.

## Verification

The export adds **455 modules**: the `HigherDimLQGContinuity` modules of the closure (88,410 lines in 454
files), and `HigherDimLQGMetric/Sec4/Bridge.lean` of an earlier library, copied byte-for-byte from
development commit `e673af9df85cce0c4a373317a508da7bc93dd62a` (the release commit; the last three frozen
theorems were sealed in `7ed6a9d94`, and the exported files are the same at both commits). The local
import closure of the five frozen theorems has **3,339 modules**: 454 HigherDimLQGContinuity, 1,300
HigherDimLQGMetric, 734 QuantumZipper, 667 LQGMetric, 97 HigherDimLFPP, 49 GaussianLQG and 38
LQGDimension. The other 2,884 were already part of this release and are byte-identical.

- **Kernel replay (development workspace).** `lake env leanchecker --fresh` on the development root
  module, which imports the five frozen theorem modules and the rest of the library, re-checked in a
  fresh environment every declaration of their closure, Mathlib included: exit code 0 on 22 October 2026,
  11:24–11:33 CEST, in 8 min 34 s, on the Lean sources of commit `e673af9df`.
- **Fresh build and focused certificate (this export).** The 455 new modules were **compiled afresh from
  the exported files**, with the public verifier's per-module settings (`lean -j1 -M8192`): 1,092 seconds
  of wall time, at most 16.1 seconds and 5.2 GB per module. The 2,884 previously released dependencies
  were reused after all closure files were checked byte-for-byte. [`Check.lean`](Check.lean) was then
  compiled afresh and **passed**. It checks the verbatim statements of the five theorems, derives that
  the hypotheses of the version clause can be met, prints the frozen definitions, and checks the
  section-level results (16 axiom reports). It rejects `sorry` and audits **46,485 project declarations
  and 131,575 reachable declarations**, allowing only `propext`, `Classical.choice` and `Quot.sound`. See
  [verification.json](verification.json), which also records the SHA-256 of every frozen file.
  `leanchecker --fresh` then replayed this build: exit code 0 (8 min 26 s), through a scratch module that
  imports the five frozen theorem modules.
- The [public workflow](https://github.com/leobon12/lean-formalizations/actions/workflows/verify.yml)
  rebuilds every module from source and runs the combined [certificate](../../Certificate.lean), which
  includes these theorems.

To reproduce from the public repository:

```sh
lake exe cache get
lake build HigherDimLQGContinuity.Frozen.Theorem11Metric HigherDimLQGContinuity.Frozen.Theorem11 \
  HigherDimLQGContinuity.Frozen.Theorem11Xi HigherDimLQGContinuity.Frozen.Prop18 \
  HigherDimLQGContinuity.Frozen.MedianOneStrongExists
lake env lean results/higher-dimensional-lqg-continuity/Check.lean
for m in Theorem11Metric Theorem11 Theorem11Xi Prop18 MedianOneStrongExists; do
  lake env leanchecker --fresh HigherDimLQGContinuity.Frozen.$m
done
sha256sum HigherDimLQGContinuity/Frozen/*.lean    # compare with frozen_statement_files in verification.json
```

`Check.lean` runs `#print axioms` on each theorem; the expected output is `[propext, Classical.choice,
Quot.sound]`. `leanchecker --fresh` accepts a single module, hence the loop; each run replays Mathlib as
well. The first module already covers Theorem 1.1 with its whole proof.

The sources are published byte-for-byte. Their docstrings cite development documents that are not part of
this snapshot: the corrected rewrite ("blueprint"), rulings (such as N11 above), audits, work packets,
the interface plan and the frozen-anchor manifest. They also mention `Improve/Rounding.lean`, development
files outside the closure of the theorems, which are not part of this snapshot. Kernel checking
establishes the Lean proofs; correspondence with the paper is the subject of the conventions above.

## Credits

The paper builds on Ding–Gwynne–Zhuang [1] (arXiv:2310.03996), Contreras Hip–Zhuang [2]
(arXiv:2512.06292) and [3] (arXiv:2504.09141), Ding–Gwynne [4] (arXiv:2110.00177), Chen–Dafnis–Paouris
[5] (arXiv:1306.2410), Hatcher [6] (*Algebraic Topology*, §3.3) and Kavvadias [7] (arXiv:2509.15544), and
on the supplied manuscripts [8]–[10]. The formalization reuses the [higher-dimensional exponential
metrics](../higher-dimensional-lqg-metric/), [higher-dimensional LFPP](../higher-dim-lfpp/), [LQG
metric](../lqg-metric/), [Gaussian LQG distance](../gaussian-lqg-distance/), [small-parameter LQG
dimension](../small-gamma-dimension/) and [Quantum Zipper](../quantum-zipper/) releases. The original
mathematical results are due to their authors; source-file attribution is retained. The statements were
frozen and audited following Scott Armstrong's
[LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) workflow.

[All released formalizations](../../README.md)
