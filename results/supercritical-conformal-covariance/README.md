# Conformal covariance of the supercritical Liouville quantum gravity metric

**Status.** Both frozen theorems, Theorem 1.1 and realization independence, are `PROVED` (two keys each), and the supporting theorems below are proved and independently audited.

This Lean 4 project formalizes Theorem 1.1 of *Conformal covariance of the supercritical Liouville quantum gravity metric*, revised October 1, 2026, an **AI-generated, unrefereed draft**: [the manuscript PDF at the pinned revision](https://github.com/leobon12/ai-generated-mathematics/blob/51d7c1283f87c885c070a1a373e116af7e30b0b1/papers/supercritical-conformal-covariance.pdf) of `leobon12/ai-generated-mathematics` (commit `51d7c1283`, SHA-256 `d5efcdbb7cf5ac8db89e9ecb105bca4c5d1c45ec17a0ceebb8f9feb33dbfaf9b`). The PDF is not copied here, but its pinned plain-text extraction is: [source/supercritical-conformal-covariance.txt](source/supercritical-conformal-covariance.txt) (SHA-256 `7780c858aae06ba251c02516164f0ea4edd3835c7aeb1fc3e8dcf375db55f603`). Line numbers “l. N” of the manuscript, in this guide and in the Lean files, are lines of that file; line numbers of Ding–Gwynne (DG, arXiv:2110.00177v3) and Gwynne–Miller (GM, arXiv:1905.00384v2; GMU, arXiv:1905.00383v3) refer to the arXiv TeX sources.

In words: for ξ above ξ_crit and Q = Q(ξ), a conformal bijection φ : U → V transports the domain metric of a GFF plus continuous function h on V exactly to the domain metric of h ∘ φ + Q log|φ′| on U. Equality holds almost surely for all pairs at once, including singular endpoints, with values allowed to be infinite. The probability-one event may depend on φ.

| Result | Lean declaration | Status |
| --- | --- | --- |
| Theorem 1.1 | `SupercriticalConformalCovariance.conformal_covariance` (frozen) | **PROVED** (two keys): key 1 sealed in development commit `4e8c611b7` (body `by exact SupercriticalConformalCovariance.Implementation.conformal_covariance_impl`; standard axioms only); independent key-2 audit `SEAL-AUDIT-conformal_covariance_v1.md`, `VERDICT: PASS`, development commit `523ae06cc` |
| Realization independence | `SupercriticalConformalCovariance.domainMetric_ae_eq_of_isDomainRealization` (frozen) | **PROVED** (two keys): key 1 sealed in development commit `ef4f163b7`; independent key-2 audit `SEAL-AUDIT-domainMetric_ae_eq_of_isDomainRealization_v1.md`, `VERDICT: PASS`, development commit `5d0efcd44` |
| Theorem 1.1 for every ξ > 0 ([below](#theorem-11-for-every-ξ--0)) | `SupercriticalConformalCovariance.Root.conformal_covariance_all_xi` | Supporting theorem: proved from the same inputs as Theorem 1.1, without the hypothesis ξ > ξ_crit; not frozen and not sealed; audited by `Check.lean` |
| Gwynne–Miller's Axiom IV for one field law ([below](#additional-result-gwynnemiller-form-corollaries)) | `SupercriticalConformalCovariance.GMForm.gm_axiomIV_on_base` | Supporting theorem, derived from the frozen Theorem 1.1; independently audited; not frozen and not sealed |
| Gwynne–Miller's Axiom IV for countably many laws and maps | `SupercriticalConformalCovariance.GMForm.exists_countably_universal_gm_axiomIV_on_base` | Supporting theorem, as above |
| Gwynne–Miller “one map for every law” form | none | **OPEN.** Not proved and not claimed. |

## Exact frozen theorem statement

The following declaration head is copied from the author-approved frozen file. The proof body is omitted here; the first seal key replaced the registered draft body `by sorry` by `by exact SupercriticalConformalCovariance.Implementation.conformal_covariance_impl` and left the head unchanged. Its quantifier order is part of the statement.

```lean
theorem conformal_covariance :
    ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
      ∀ U V : Opens ℂ, IsConnected (U : Set ℂ) → IsConnected (V : Set ℂ) →
      IsGreenian U → IsGreenian V →
      ∀ (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V),
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C(V, ℝ)),
        IsDomainRealization V P h h₀ f →
        (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
            (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)), MeasurePreserving π P' P ∧
          IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k) ∧
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (π : Ω' → Ω), MeasurePreserving π P' P →
          ∀ (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
            IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k →
            ∀ᵐ ω' ∂P', ∀ u v : U,
              domainMetric (ξ : ℝ) D V (h₀ (π ω')) (f (π ω'))
                  (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) =
                domainMetric (ξ : ℝ) D U (g₀ ω') (k ω') (u, v) :=
```

The separate realization-independence statement is also frozen, and it is `PROVED`. Its seal replaced the draft body by `by exact SupercriticalConformalCovariance.Implementation.domainMetric_ae_eq_of_isDomainRealization_impl` and left the head unchanged. The frozen file's module comment predates that seal and still calls the body a draft placeholder; see [Immutable frozen comments](#immutable-frozen-comments). The frozen head is:

```lean
theorem domainMetric_ae_eq_of_isDomainRealization :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
      ∀ V : Opens ℂ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn V) (h₀ h₀' : Ω → DistC) (f f' : Ω → C(V, ℝ)),
        IsDomainRealization V P h h₀ f → IsDomainRealization V P h h₀' f' →
        ∀ᵐ ω ∂P, domainMetric (ξ : ℝ) D V (h₀ ω) (f ω) = domainMetric (ξ : ℝ) D V (h₀' ω) (f' ω) :=
```

## Statement scope and meaning

These six disclosures are part of the approved statement, and matter when comparing it with the printed theorem:

1. **Greenian domains.** Both connected open domains are assumed `IsGreenian`, the zero-boundary GFF admissibility condition. This is the author's A14 restriction of the manuscript's unrestricted domains. Disks and bounded domains satisfy it; ℂ and ℂ minus a point do not. Its classical interpretation is a non-polar complement; that equivalence is not a Lean theorem here.
2. **Global realization field class.** `IsDomainRealization V P h h₀ f` means h = h₀|_V + f almost surely, with h₀ a whole-plane GFF plus continuous function and f a measurable random continuous function on V. This is narrower than a class defined by merely local decompositions. For example, the field obtained by composing a suitable whole-plane GFF with z ↦ z² on the punctured disk has local decompositions of the required kind but no single global realization of this form. The Gwynne–Miller-form corollaries [below](#additional-result-gwynnemiller-form-corollaries) restate the result for Gwynne–Miller's zero-boundary field class.
3. **Strong metric.** The theorem quantifies over every `D` satisfying `IsStrongLQGMetric ξ Q D`. This reads the paper's “one normalization” using the strong metric uniqueness theorem: all normalizations differ by a positive deterministic factor, and the covariance factor is one for each.
4. **Literal critical threshold, verified unused.** `xiCrit` is the infimum of positive parameters whose LFPP exponent is 2, and the frozen theorem keeps the paper's hypothesis `xiCrit < ξ` as printed. (Lean's convention `sInf ∅ = 0` could only weaken that premise.) A probe of the compiled proof shows that the hypothesis is never used: it is passed through the provider's wrappers to four inputs, and each of them discards it; no fact about `xiCrit` enters the proof. The supporting theorem `conformal_covariance_all_xi` therefore states Theorem 1.1 without it, see [below](#theorem-11-for-every-ξ--0). The frozen theorem itself is unchanged.
5. **Two inlined definitions.** The frozen `confPushTest` spells out the test-function transport used by `SmallGammaGeodesics.confPullFun`; frozen `IsGreenian` spells out `LQGMetric.ZBAdmissible`. Each was checked `rfl`-equal to its library counterpart during statement approval. Their frozen bodies protect the meanings against a changed upstream definition.
6. **Existence clause.** The first conjunct constructs a measure-preserving extension carrying a realization of the pulled-back field. This makes the right-hand domain metric genuinely defined and prevents the universal equality clause from being vacuous. The construction requires a Markov decomposition on arbitrary Greenian domains and a coupling; it is a proof obligation of the root theorem.

`domainMetric ξ D V h₀ f` is Weyl scaling by f of the whole-plane metric D(h₀), restricted to paths in V; `weylScaleOn` is its path-length infimum and can take `∞`. `confPullbackField` acts on distributions through the frozen test-function map and adds Q log|φ′|. The separate frozen realization-independence theorem says that two realizations of the same domain field give the same domain metric almost surely, with no Greenian premise.

## Theorem 1.1 for every ξ > 0

`SupercriticalConformalCovariance.Root.conformal_covariance_all_xi` (module `Root.AllXi`) is the frozen statement of Theorem 1.1 with the hypothesis `xiCrit < ξ` removed: for **every** ξ > 0, Q = Q(ξ) and every strong LQG metric D with parameter ξ, the conclusion of Theorem 1.1 holds, with the same Greenian domains, field class, existence clause and almost-sure equality for all pairs. It is proved from the same landed inputs as the frozen theorem (ruling A23). It implies the frozen theorem, and the frozen type is, by `rfl`, `∀ ξ, xiCrit < ξ →` its type at ξ; `Check.lean` checks both facts. So the statement audits of Theorem 1.1 apply to it apart from that binder. Strong LQG metrics exist for every ξ > 0, and are unique up to a deterministic positive factor, by the sealed results of `SupercriticalLQGUniqueness` (Ding–Gwynne, Theorem 1.8). So covariance holds for the strong metric of every ξ > 0, including ξ = ξ_crit and ξ < ξ_crit.

What this does and does not say. It is a theorem about Ding–Gwynne's strong LQG metrics, the objects of the frozen statement, for every parameter. It is not frozen and not sealed: it strengthens the approved statement without replacing it, and Theorem 1.1 is the frozen theorem as approved. It does not by itself identify these metrics, for ξ < ξ_crit, with the subcritical metric of Gwynne–Miller; that identification is not part of this release.

## What is in the library

The library `SupercriticalConformalCovariance` ships 262 Lean files: the 256 files of the seal commit `4e8c611b7` of Theorem 1.1 (unchanged in `f0980fc71`, which records key 1) and the six modules of the supporting theorems that landed after the seal (`5e22c7791`). The aggregator `SupercriticalConformalCovariance.lean` is not shipped. The table groups the directories by the part of the manuscript they
prove. *Lines* are physical lines of the development files, as `wc -l` counts them; *code lines* are the lines that are neither blank nor
entirely inside comments (computed with the public verifier's comment stripper). The files were listed with `git ls-files` at that commit,
recounted at development commit `a80b9333f`, which contains all 262.
The shipped files differ only by the comment edits described in [About the source files](#about-the-source-files), so their code lines are
the same.

| Part | Directories | Modules | Lines | Code lines |
| --- | --- | ---: | ---: | ---: |
| Domain fields and domain metrics; realization independence (§1, GMU Remark 1.5) | `Domain`, `Transport`, `Compact`, `Conf` | 23 | 2,840 | 2,211 |
| Conformal change of the field: zero-boundary GFF under conformal maps, Markov decomposition on Greenian domains, existence of the pulled-back realization, reversal | `ZBConformal`, `Markov`, `GPull`, `Reversal` | 39 | 4,477 | 3,856 |
| Lemma 2.1, the uniform comparison with C = C(ξ) (Koebe distortion, affine and rotation covariance) | `BiLip`, `Univalent`, `Rotation` | 41 | 9,381 | 7,682 |
| Input (I4): Gwynne–Miller Lemma 2.4, with Miller–Sheffield IG4 Prop 2.10 and total-variation bounds | `GM24`, `TV` | 35 | 5,624 | 4,720 |
| Lemmas 3.1–3.3: confined metrics and the tangent limit | `Lemma31`, `Tangent` | 29 | 5,150 | 4,005 |
| §4: regular geodesics, measurable selection, Proposition 4.3 | `Small`, `P43Final`, `Selection`, `Regular`, `Recovery` | 52 | 7,527 | 6,665 |
| §5: good annuli, Lemma 5.1, the covers of display (10) | `GoodAnnulus`, `Good`, `Cover` | 14 | 2,625 | 2,179 |
| §6: Proposition 6.1, the optimal constant is one | `Improve` | 1 | 1,487 | 1,375 |
| §7 and the assembly of Theorem 1.1, with its all-ξ form | `Root` | 8 | 1,179 | 940 |
| The Gwynne–Miller-form corollaries and their support | `GMForm` | 8 | 1,145 | 1,038 |
| **Proof modules** | | **250** | **41,435** | **34,671** |
| Frozen statements (8 definitions, 2 theorems) | `Frozen` | 10 | 388 | 198 |
| Providers of the two frozen theorems | `Implementation` | 2 | 89 | 57 |
| **Total shipped** | | **262** | **41,912** | **34,926** |

The proof also uses these already released libraries, unchanged (3,761 modules of their import closure):

| Library | What it supplies here |
| --- | --- |
| `SupercriticalLQGUniqueness` (Ding–Gwynne, uniqueness of the critical and supercritical metrics; 1,492 modules, plus its six top-level support modules `SLUSupport`, `SLUMetricAPI`, `SLUMetricAPI2`, `SLUFieldSupport`, `BR1Bridges`, `NV1Evidence`) | the strong LQG metric and its axioms (`IsStrongLQGMetric`, `IsLFPPExponent`, Weyl scaling, lower semicontinuous metrics), strong metric uniqueness, the annulus tail bounds, the two-scale estimates of the good-annulus events (with the repaired Lemma 3.14 steps), Pfeffer's loop chaining, the escape-barrier repair, and the topology of lower semicontinuous functions |
| `LQGMetric` (Gwynne–Miller, existence and uniqueness for γ ∈ (0,2); 1,356 modules) | whole-plane and zero-boundary GFFs, `IsGFFPlusCont`, zero-boundary admissibility (`ZBAdmissible`, the body of `IsGreenian`), Markov and Weyl tools, internal metrics and geodesics, measurability tools |
| `QuantumZipper` (Sheffield's quantum zipper; 769 modules) | univalent function theory and the Koebe distortion theorem, harmonic parts of the GFF, local total-variation bounds |
| `SmallGammaGeodesics` (18 modules) | the subcritical conformal covariance machinery `CC` (conformal test-function pullback `confPullFun`, universal locality, pullback convergence), test functions |
| `LQGDimension` (107 modules) | dependencies of the libraries above (no direct import) |
| `GaussianLQG` (9 modules) | affine and rotation transport of fields and LFPP metrics |
| `HigherDimLQGMetric` (4 modules) | curve reparametrization |

## Additional result: Gwynne–Miller-form corollaries

Gwynne–Miller's subcritical conformal covariance (arXiv:1905.00384v2, Definition 1.1 and Axiom IV, TeX l. 272–290) is phrased differently from Theorem 1.1. The field lives on the source domain, the field class is “zero-boundary GFF plus a continuous function”, and the metric is a measurable function of the field. Ruling A13 adds this form as a corollary of Theorem 1.1 and realization independence. The corollaries below are **supporting theorems** in `SupercriticalConformalCovariance.GMForm`: they apply the frozen Theorem 1.1 and need no hypothesis beyond the mathematical ones, but they are not frozen and not sealed. Two independent statement audits compared them with Gwynne–Miller's definitions: the first found six points, which ruling A21 settled by strengthening the statements; the second, on the final statements, passed. `Check.lean` audits each of them.

**Setting.** ξ > ξ_crit (these corollaries keep the frozen theorem's hypothesis), Q = Q(ξ), D a strong LQG metric, U a connected Greenian domain, and φ : U → V a conformal bijection; then V is connected and Greenian too, so the main forms assume nothing about V. A random distribution h on U is in **Gwynne–Miller's class** if, almost surely, h = z + f, where z is a zero-boundary GFF on U and f is a measurable random continuous function on U, both given on the probability space of h. Here f may depend on z and need not extend continuously to ∂U. The transformed field is h^φ := h ∘ φ⁻¹ + Q log|(φ⁻¹)′| on V. *The domain metric of h* means the domain metric of a whole-plane realization of h, as in the statement section above; by realization independence it does not depend on which realization is used.

**Main forms: Axiom IV on the field's own probability space.**

- `gm_axiomIV_on_base` (one field law). For h in Gwynne–Miller's class on U there are measurable maps Φ_U : 𝒟′(U) → (U × U → [0, ∞]) and Φ_V : 𝒟′(V) → (V × V → [0, ∞]) such that:
  - *both maps are versions of the metric:* on every measure-preserving extension of the probability space and for every whole-plane realization there, Φ_U(h) is almost surely the domain metric of h, and Φ_V(h^φ) is almost surely the domain metric of h^φ;
  - such realizations exist (on a product extension of the probability space);
  - *Axiom IV:* almost surely **on the probability space of h itself**, Φ_U(h)(u, v) = Φ_V(h^φ)(φ(u), φ(v)) for all u, v ∈ U.
- `exists_countably_universal_gm_axiomIV_on_base` (countably many laws and maps). For a countable family of fields h_i in Gwynne–Miller's class on U, each on its own probability space, and conformal bijections φ_i of U onto the same V, one pair Φ_U, Φ_V, chosen before the index, has the three properties above for every i, with φ_i in place of φ.

In plain terms (from the second audit): for any specified such field, there are measurable functions of the field on U and on V that agree with the metric on every realization extension and satisfy Gwynne–Miller's Axiom IV on the field's original probability space, almost surely for all endpoint pairs at once, with exact constant one and infinite distances allowed; one pair of functions works for any specified countable family of fields and of conformal maps between the same two domains. The version clauses rule out trivial maps such as Φ_U = Φ_V = 0. One choice for all the laws comes from realization independence and a coin mixture of the countably many laws; the identity is moved from the extension down to the base space by disintegration.

**Intermediate statements, on extensions of the probability space.** They are proved and audited as well, but each is weaker than the main forms as a stand-alone claim, because its almost-sure identity lives on an extension:

- `gm_direction_of_root`: for a field h on U with a whole-plane realization, the conclusion of Theorem 1.1 for φ⁻¹ : V → U, on every measure-preserving extension carrying a realization of h^φ (and such an extension exists). This turns the manuscript's convention into Gwynne–Miller's.
- `gm_zeroBoundary_covariance_on_extension`: for h in Gwynne–Miller's class, extensions carrying whole-plane realizations of h and of h^φ, on which the same almost-sure equality holds for all u, v ∈ U.
- `exists_fieldwise_gm_axiomIV_on_extension` and `exists_countably_universal_gm_axiomIV_on_extensions`: measurable maps as above, one law or countably many laws with φ fixed, with the Axiom IV identity on an extension.

**Gwynne–Miller's literal Definition 1.1: OPEN.** For each Greenian domain U, take one measurable map Φ_U, chosen before any field. It must satisfy two conditions:

- for **every** field h in Gwynne–Miller's class on U, on every probability space, Φ_U(h) is almost surely the domain metric of h;
- Axiom IV holds: for every conformal bijection φ : U → V and every such h, almost surely, Φ_U(h)(u, v) = Φ_V(h^φ)(φ(u), φ(v)) for all u, v ∈ U.

The coin-mixture argument handles only countably many laws. No known countable family dominates Gwynne–Miller's class, which allows all random continuous corrections on all probability spaces. This form is **neither proved nor claimed**. Its failure is not claimed either.

**Scope differences that remain in all forms.** Gwynne–Miller's Definition 1.1 ranges over all open sets, including disconnected ones and the whole-plane case. Here the domains are connected and Greenian (ruling A14). Without the Greenian assumption, no zero-boundary GFF exists, for example on ℂ minus a point. On ℂ itself, Gwynne–Miller use the whole-plane GFF instead. For complex-affine maps of ℂ (their Axiom IV′) the landed `SupercriticalConformalCovariance.Rotation.ae_complex_affine_covariance` gives the covariance with D itself as the one map for every law; that every conformal self-map of ℂ is affine is not formalized here. The Gwynne–Miller-form layer restates Axiom IV and measurability; the domain forms of Axioms I–III are in `SupercriticalConformalCovariance.Domain.Axioms`. Gwynne–Miller allow any coupling of h with a continuous function; here the decomposition is supplied on the probability space under discussion. The supercritical metric is lower semicontinuous and may be infinite, including at singular endpoints. The probability-one event depends on φ. Gwynne–Miller's Theorem 1.3 prints “φ : ℂ → U” (TeX l. 327). Axiom IV's convention U → φ(U) is the coherent reading and is used here.

## How it was checked

The project follows Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) workflow, in this order.

1. **Statement.** The theorem and its meaning-carrying definitions were transcribed from the manuscript, elaborated as candidate files, audited by two independent statement audits ([record](records/STATEMENT-AUDITS.md)), approved by the author ([approval extract](records/APPROVAL-REQUEST.md); ruling A15), and frozen in ten one-declaration files whose bytes are pinned by a hash manifest. The shipped `check_frozen_anchors.py` rechecks those hashes.
2. **Source dependency graph.** Every step of the manuscript's proof, every cited input and every repair is a node of a reviewed dependency graph (revision 7: 214 nodes and 456 edges, all reviewed by an independent global reviewer). Its 40 explicit gap nodes are listed [below](#source-repairs-and-explicit-gaps); an independent auditor checked every repair ([public extract](records/SOURCE-GAP-AUDIT.md)).
3. **Proof.** The Lean proof follows that graph. Each frozen theorem has a provider theorem with exactly the frozen statement. Theorem 1.1's first seal key passed in development commit `4e8c611b7` (rehearsal on the exact commit, the body change, checker, build, standard axioms for the export and the provider, `leanchecker --fresh`); its key-2 audit `SEAL-AUDIT-conformal_covariance_v1.md` returned `VERDICT: PASS` at development commit `523ae06cc`.
4. **Two-key proof seal.** A theorem is `PROVED` only after both keys. *Key 1:* after a rehearsal on the exact commit, the frozen body is changed only to `by exact <provider>`; the frozen-anchor checker, the build, `#print axioms` and an independent kernel replay (`leanchecker --fresh`) must pass. *Key 2:* a fresh auditor, who did no earlier work on that theorem, re-derives the statement's fidelity to the manuscript, looks for proof steps smuggled in as hypotheses, checks the axioms, replays the kernel check, and judges every graph-consumption record (next item).
5. **Graph consumption at the seal.** For the part of the graph that proves the sealed theorem, each edge “node A uses node B” is checked against the Lean proof: the edge is *consumed* when the Lean declaration mapped to A uses the one mapped to B at term level. Every edge that is not consumed must be covered by a written deviation record, which states why the Lean proof does not need that edge. The main reasons are:
   - **bypass:** the Lean proof reaches A's conclusion by a route that does not pass through B, for example a stronger or more general lemma, and the record names that route;
   - **discharged at the consumer:** A's Lean lemma takes B's content as a hypothesis, and a named caller inside the proof supplies it, so the step is proved, not assumed;
   - **definition context:** B is a definition or convention that A uses through its statement, not as a lemma;
   - **frozen-definition context:** an edge between two frozen definitions, which never refer to each other in Lean; it is judged against the frozen definitions themselves.

   *Realization independence* (ruling A18): the records include two bypasses limited to this theorem, five premises discharged inside the proof, and three frozen-definition context edges. A fresh reviewer accepted all of them, and the key-2 auditor judged them again; its verdict was `PASS`.

   *Theorem 1.1* (ruling A20): the part of the graph that proves Theorem 1.1 has 202 nodes and 421 edges. 236 edges are consumed at term level. 189 records cover the rest: 87 bypasses, 61 discharged at the consumer, 31 definition context, 3 premises supplied by the consumer's caller, 3 frozen-definition context, 2 applied directly by the provider, 1 definition component, and 1 normalization step of Proposition 4.3 proved inline. Three fresh reviewers judged every record against the Lean proof, with Lean probes. They rejected none, and their 50 corrections to the graph-to-Lean map turned 41 deviations into consumed edges. A short recheck of the five records changed by the merge accepted all of them. On the landed development build, the consumption check reports no failure, with rows identical to the reviewed run. The key-2 auditor judged each record again, and a record whose justification is false fails the seal, even when its edge is harmless: its first round failed on this step alone, because nine graph-to-Lean references did not state their nodes' content and, on the corrected map, three rows were neither consumed nor covered by a record; after the correction (ruling A20.1: nine references fixed, three records added, one record text corrected; 241 edges consumed, 184 deviation rows, no failure), the auditor's first re-check found one of the new record texts false (it named a declaration outside the proof closure) and failed again; that text and one more were corrected, with no change to any graph row, and the second re-check returned `VERDICT: PASS` (development commit `523ae06cc`).
6. **Landing.** The proof of Theorem 1.1 entered the development library as the import closure of its provider (234 new modules). The landed library builds; its only `sorry` is the registered draft body of the frozen Theorem 1.1; every landed constant depends only on the standard axioms; and the provider's type is equal, as a Lean expression, to the frozen statement. The supporting theorems landed afterwards with their six modules (development commit `5e22c7791`).
7. **Supporting theorems.** The all-ξ theorem rests on a probe of the compiled proof showing that the hypothesis ξ > ξ_crit is never used (ruling A23). The Gwynne–Miller-form corollaries were audited twice: the first independent audit found six points, which ruling A21 settled by strengthening the statements; the second, on the final statements, passed (A22.7). Public extracts: [the probe](records/XI-PROBE.md), [the first audit with A21's dispositions](records/GM-FORM-AUDIT-1.md), [the second audit](records/GM-FORM-AUDIT-2.md); the [statement audit record](records/STATEMENT-AUDITS.md) lists all of them. They are not frozen and not sealed; `Check.lean` audits their axioms with the frozen theorems, and checks that the all-ξ theorem implies the frozen one.
8. **Release checks.** Every new module (the 262 files of this library and the 1,498 comment-stripped modules of the released `SupercriticalLQGUniqueness` family) was compiled from empty project artifacts, against 2,263 released modules whose oleans are trace-linked to the public bytes. That build used a tree equal to the release bytes except for the module doc of `GM24/Main.lean`, whose release bytes were then compiled against the same build. No error, no `sorry`. On the release tree (development commit `a80b9333f` staged onto the public `main`), `Check.lean` reports only `propext`, `Classical.choice` and `Quot.sound` for each of the 9 advertised theorems and checks that the all-ξ theorem implies the frozen one; `check_release.py`, the public source scan and the release lint pass.

## Immutable frozen comments

The ten frozen files ship byte for byte as sealed: what the seals certify are those exact bytes, so no release edit touches them, not even a comment. Their comments therefore keep 38 references to the development process, in 10 files. Each one is listed, with its file, line and text, in [the frozen-reference inventory](records/FROZEN-INVENTORY.json), and the release lint fails on any frozen reference that is not in it. They fall into five classes:

| Class (count) | What the frozen comment prints | Public record |
| --- | --- | --- |
| approval locator (10) | the private path `planning/candidates/rev2.2/APPROVAL-REQUEST.md` of the approval request | [Approval request extract](records/APPROVAL-REQUEST.md), with the request's SHA-256 and its six statement disclosures |
| candidate file (10) | the name and hash prefix of the approved candidate file, such as `CandConformalCovariance.lean` | [Approval request extract](records/APPROVAL-REQUEST.md), with the table of candidate files and their full SHA-256 |
| ruling (15) | rulings A10.2, A14 and A15 | [Rulings excerpt](records/RULINGS-EXCERPT.md) |
| literature locator (1) | the private copy `source/literature/gm-uniqueness/tex/uniqueness-final.tex` of a TeX source | [Gwynne–Miller Remark 1.5 reference](records/GM-UNIQUENESS-REFERENCE.md) |
| stale status (2) | the words “DRAFT_SORRY placeholder until the two-key seal” in the two theorem files | this guide: the status table above is authoritative. The comments were written at the freeze, before any seal |

The line numbers printed in the frozen docstrings follow the conventions stated at the top of this guide; the public `frozen-anchor-manifest.json` records them in its `source.revision` field.

## Proof route

The source graph traces the manuscript's Sections 1–7: the strong metric and domain interface; conformal GFF comparison and a uniform local comparison; convergence of confined metrics; regular geodesics and measurable selection; good annulus events and covering; improvement of the optimal comparison constant to one; and extension from whole-plane to Greenian domain fields. The Lean proof follows it, with three route choices where the graph offers alternatives: Euclidean continuity of finite-length paths comes from lower semicontinuity and the escape barrier (logically prior to Pfeffer's printed route, which presupposes it); Lemma 3.3 passes from almost-sure and total-variation convergence of the fields to the metrics by a transfer lemma; and Proposition 4.3 uses a Skorokhod representation with Jankov–von Neumann measurable selection. The proof uses the sealed Ding–Gwynne results in `SupercriticalLQGUniqueness`, domain fields in `LQGMetric`, univalent function theory in `QuantumZipper`, and the subcritical conformal covariance machinery in `SmallGammaGeodesics`; see [What is in the library](#what-is-in-the-library).

## Source repairs and explicit gaps

The manuscript is AI-generated and unrefereed. Some of the results it cites also have printed proofs that are incomplete in places. Every repair that the formal route needs is a node of the source dependency graph. At graph revision 7, after an independent audit of every repair ([public extract of the audit](records/SOURCE-GAP-AUDIT.md)), **40 nodes are explicit source gaps**: 30 in the manuscript and 10 in the cited literature. A gap whose faulty step is printed in a cited proof but reproduced in the manuscript's own argument is listed under the manuscript and marked *inherited*.

Each line gives the graph node and a one-line summary. A listing here is not a proof-status claim. The Lean proof of Theorem 1.1, which carries out these repairs, has landed; a repair counts as proved in Lean when Theorem 1.1 is `PROVED`. No repair changes the frozen statements. Manuscript line numbers (l.) refer to its pinned text extraction. Literature line numbers refer to the arXiv TeX sources of the pinned versions.

The audit's severity classes are:

- **F**: a false printed statement;
- **P**: a gap in a printed proof;
- **C**: an imprecise citation;
- **N**: a convention or notation issue.

*(minor)* marks a real omission that a short standard argument repairs.

### Gaps in the manuscript (30)

**F: false printed statement (1)**

* `lem-3.1#repaired` — Lemma 3.1 (l. 163–167) is ill-posed as printed. Its hypotheses allow arbitrary generalized functions, and the couplings need not carry the continuous corrections. In one literal reading, “jointly with the fields” on the larger neighbourhood is false: take g_n = g + ψ with ψ supported off K′. The lemma is true in its natural reading, but the proof (l. 169–170) needs one common locality functional. The formal route uses a repaired, internal statement; the root does not consume Lemma 3.1 directly.

**P: gaps in printed proofs (19)**

* `lem-4.1#connector` — Lemma 4.1 proof (l. 275–278). The connector bound pays only up to radius s_j, but the loop may lie near radius √s_j, so the radial segment in between is unpaid. The repair uses two scales (s_k > √s_j). The statement is unchanged.
* `lem-2.1#loop-chaining` — Lemma 2.1 proof (l. 139–144), *inherited* from Pfeffer's proof of Lemma 2.26. The chained loops need not form a connected set, and the terminal loop is never paid for. Repaired by a filled-set chain.
* `prop-6.1#endpoint-exclusion` — Prop 6.1 proof (l. 471–479, 494–496). “Ignore the initial and terminal portions” does not ensure that both endpoints lie outside B_{2r_j}(z_j), which the loop arguments need. Repaired by a last-exit/first-entry corridor.
* `lem-3.3#fixed-confinement` — Lemma 3.3 proof (l. 218–223). The maximal coupling plus Lemma 3.1 needs one locality functional valid for the n-dependent laws, and a gluing with h.
* `lem-3.3#transfer-lemma` — A repair component of the previous item. Almost-sure and total-variation convergence of the fields give convergence in probability of Borel functionals of the fields.
* `domain-measurable-functional` — l. 233. “The metric is a measurable functional of that field” needs one Borel functional valid for the laws h^{ψ_n} and h^a at once. The metric axioms give one functional per law.
* `universal-locality` — l. 169–170 and 233 compare the metrics of fields with different laws through “determined by”, but the locality axiom gives one functional per law. Repaired by a coin mixture of countably many laws.
* `g-pull` — l. 26, 37 and 544–545 tacitly use that h ∘ φ + Q log|φ′| is again a GFF plus a continuous function. Proved for Greenian U, V by a Markov decomposition, conformal invariance of the zero-boundary GFF, and re-embedding into a whole-plane field.
* `sec5#g1-probability` — (G1) (l. 383–389), *inherited* from Ding–Gwynne's proof of their Lemma 3.14. The ratio bound around ≤ δ^θ · across does not follow from DG Lemma 2.13, which bounds around-distances by δ^θ times the elapsed geodesic time. Repaired by the two-scale ratio estimate sealed in `SupercriticalLQGUniqueness`.
* `sec5#g3-probability` — (G3) (l. 393–395), *inherited* from the same DG proof. DG Lemma 2.14 needs geodesic endpoints in an open set away from the curve, but these geodesics end on the annulus boundary. Repaired by the closed-endpoint extension sealed in `SupercriticalLQGUniqueness`.
* `lem-1.2#metric-curve` *(minor)* — Lemma 1.2 proof (l. 83–87). The proof must show that the uniform limit of the paths is a metric curve, as the internal metric requires. A lower semicontinuity argument does this.
* `lem-3.3#expanding-confinement` *(minor)* — Lemma 3.3 proof (l. 224–230). The strict barrier event is not stable under the non-constant Weyl correction Q log|(ψ_n⁻¹)′| + Q log|a|. The repair uses a Borel, local margin event “around < θ · across” with θ < 1. The interchange of limits in the same paragraph is standard; see the reading notes.
* `lem-3.3#joint-identification` *(minor)* — Lemma 3.3 proof (l. 231–236). Identifying the subsequential limit needs a Polish coordinate for the field and the measurable graph of h ↦ D_h.
* `lem-4.2#borel-witness` *(minor)* — Lemma 4.2 proof (l. 302–322). Condition (7) involves the circle average, which is field data, so it is read as d(u, v) ≤ M. Measurability of around-distances and point-to-circle distances at moving centres needs short arguments.
* `lem-4.2#parameter-space` *(minor)* — Lemma 4.2. The space of pairs of lower semicontinuous length metrics is not shown to be Polish, and it is not closed. A standard Borel parameter space with measurable metric maps gives the same universally measurable selection.
* `prop-4.3#apply-tangent` *(minor)* — Prop 4.3 proof (l. 344–349). Lemma 3.3 is stated for one whole-plane GFF, but the zoomed fields vary with n, although they have one law. Applying the lemma needs the metrics to be law-determined Borel functionals. This node was added at graph revision 7.
* `prop-4.3#skorokhod` *(minor)* — Prop 4.3 proof (l. 364–366). The Skorokhod representation needs three unstated ingredients: a separable state space (countable coordinates), a mark for the failure event, and the transfer of a universally measurable event under equality of laws.
* `lem-7.1#local-decomposition` *(minor)* — Lemma 7.1 proof (l. 524–533). Coupling the zero-boundary parts with a whole-plane GFF needs an extension of the probability space that carries countably many couplings.
* `lem-7.1#pathwise-weyl` *(minor)* — Lemma 7.1 proof. Transferring e ≤ d through a random Weyl weight needs the Weyl length formula.

**C: imprecise citations (6)**

* `def:theta` *(minor)* — l. 290–291. θ is the exponent of DG Lemma 2.13 (DG §2.6), not of “Section 3.2”. This node also carries the citation slips E-P16 and E-P18 below.
* `domain-affine` *(minor)* — (I1) (l. 47–48) cites Ding–Gwynne for whole-plane fields only. The manuscript applies affine covariance to domain fields (l. 121–122, 223, 234, 344–348). The domain form is derived through realizations.
* `input-I2#escape-barrier` — (I2) (l. 51–53) attributes “every finite metric-length path is Euclidean continuous” to Pfeffer's Props 1.10 and 1.12, whose printed proofs presuppose it. The fact is supplied by an escape barrier: the ambient dyadic crossing distances diverge almost surely.
* `input-I2#escape-topology` — A repair component of the previous item. A deterministic escape lemma turns divergent crossing costs into bounded traces and Euclidean continuity.
* `input-I2#route-lsc-barrier` — The repair route itself: lower semicontinuity plus the escape barrier. This route is logically prior to Pfeffer's printed one.
* `input-I2#weyl-transfer` — A repair component. Local metric-to-Euclidean continuity passes through a locally bounded Weyl weight e^{ξf}.

**N: convention or notation (4)**

* `lem-2.1#lognormal-factor` *(minor)* — Lemma 2.1 proof (l. 124–125). The law of the log-normal factor depends on n, so it is not “independent of n”. The factor converges almost surely, so the tightness that the proof uses holds.
* `lem-2.1#uniform-centres` *(minor)* — l. 131–136. Bound (4) and Lemma 5.1 are stated for centres in K, but the lattice centres lie near K. Apply them on a compact neighbourhood of K.
* `lem-4.2#ambient-metrics` *(minor)* — Lemma 4.2. The tests in (8) use balls and annuli that leave the annulus A_{αr,r}(z). Either the compact annulus must contain them, or ambient metrics must be used.
* `lem-5.1#locality` *(minor)* — Lemma 5.1 (l. 416–417). F_{z,r} is determined by the field near the *closed* annulus, not by the field on the open annulus. The event is universally measurable, not Borel.

### Gaps in the cited literature (10)

**F: false printed statement (1)**

* `gm:lem-tv-conv#normalization` — Gwynne–Miller (2.6) and (2.8) normalize at scale |α|, but the correct scale is |α|⁻¹. As printed, both are false whenever |α| ≠ 1. This is **GM-L24-N1**; see the errata.

**P: gaps in printed proofs (8)**

* `gm:lem-tv-conv#cameron-martin` — Gwynne–Miller Lemma 2.4 proof. The Cameron–Martin shift is random, so the deterministic density bound does not apply directly; a mixture bound does. The cut-off energy also needs an L² bound.
* `gm:lem-tv-conv#decomposition` — Gwynne–Miller Lemma 2.4 proof. U_n may be ℂ, where no zero-boundary GFF exists, so disks are used instead. With the normalization (h, 𝐟) = 0, the two Markov parts are not independent, so the field is recentred. There is also a typo: φ(U_n) for φ_n(U_n).
* `gm:lem-tv-conv#harmonic-energy` — Gwynne–Miller Lemma 2.4 proof. The cited estimates from the proof of IG4 Prop 2.10 give only a sup bound. They do not give decay of the Dirichlet energy of the harmonic part. This is also an imprecise citation.
* `ig4:prop::gff_convergence#variance-bound` — Miller–Sheffield, IG4 Prop 2.10 proof (l. 1174). The bound Var(𝔥_n(y) − 𝔥_n(0)) ≤ ε² is called “not difficult to see”, with no proof and no uniformity in y. Repaired by nested disks: the variance is at most −log(1 − |y|²/L²).
* `domain-locality` *(minor)* — Gwynne–Miller (l. 319–320) assert the domain form of locality “by inspection”. It also needs one functional for several laws.
* `domain-weyl` *(minor)* — The same passage. Weyl scaling of domain metrics by corrections that may be unbounded at ∂V needs the Weyl length formula.
* `pullback-locality` *(minor)* — Gwynne–Miller (l. 362) call it “easily seen” that the pulled-back metric is local for h. The proof needs domain locality, universal locality, and test-function transport.
* `dg:prop-rotation#constant-one` *(minor)* — Ding–Gwynne Prop 1.9 proof (l. 499–501). Concluding that the constant is one from the law of D_h(0, ∂𝔻) needs P[D_h(0, ∂𝔻) < ∞] > 0. That fact is unstated and does not follow from the axioms. It does follow from Pfeffer's Prop 1.11(b): a fixed point is almost surely non-singular. The formal route uses the across-distance of A_{1,2} instead.

**N: convention or notation (1)**

* `gm:lem-tv-conv#as-conv` *(minor)* — Gwynne–Miller (2.5). The text at l. 539 has a typo: f ∘ φ_n tends to f(α⁻¹·), not to f(α·). The display itself is right. Some support details are left implicit.

### Reading notes, not errors

Before the audit, the following items were recorded as gaps. The audit found the printed text correct, or covered by the manuscript's own conventions. They record formal expansions, route choices or reading notes, and they are **not errata**.

* `disp-10#finite-family` — (10), with its existential quantifier over a continuum, contains the event for the finite test family. Lines 442–443 say which family is tested.
* `lem-2.1#endpoint-limit` — The printed argument (path compactness and lower semicontinuity of length, Lemma 1.2) is valid. The formal route is an equivalent one.
* `lem-2.1#koebe-normalized` — The printed univalent-convergence claim is correct. “After passage to a subsequence” is superfluous.
* `lem-2.1#strict-comparison` — Replacing ≤ C₀ by < 2C₀ is constant bookkeeping.
* `lem-3.2#barrier-event` — The printed event (around less than *half* of a farther crossing) is a stronger variant of the event in DG Lemma 2.11, and it is still true. A strict “around < across” would suffice. This is an imprecise citation only.
* `lem-3.2#excursion-replacement` — The manuscript already applies the surgery to distance-minimizing sequences (l. 187).
* `lem-3.2#infinite-distances` — The claim at l. 188 is true, because confined distances dominate ambient ones.
* `lem-3.3#distortion` — Standard univalent convergence, correctly invoked.
* `lem-3.3#pullback-epigraph` — ψ_n ∘ ψ_n⁻¹ is eventually the identity on compacts (Koebe ¼). That is the trivial fact behind “transported by the inverse maps”.
* The interchange of limits in Lemma 3.3 (l. 224–230), inside `lem-3.3#expanding-confinement` — “Approximates … uniformly in probability” is the standard approximation theorem for weak convergence (Billingsley, Theorem 3.2). Only the barrier transfer in that node is a gap.
* `lem-4.2#closed-annulus-trace` — Covered by l. 41: boundary endpoints use paths in the closed annulus.
* `lem-4.2#geodesic-code` — A Euclidean-continuous path of finite metric length is a metric curve. This is a formalization detail.
* `lem-5.1#shield` — The printed numerics are correct. The node only asks for a domain-metric form of the surgery.
* `prop-4.3#first-exit-confinement` — “All small endpoint annuli are contained in the rescaled domain” (l. 359–360) is the right justification.
* `markov-greenian` — A formalization extension, not an erratum. The frozen existence clause needs the Markov decomposition on arbitrary Greenian domains, while the manuscript decomposes only on disks (l. 524). Gwynne–Miller's “for each deterministic open set U” (l. 313) tacitly assumes a Greenian U.
* `thm-1.1#reversal-identity` — `SG-CC-REV-001`, **withdrawn**. The display at l. 546–547 is correct in the manuscript's forward convention: (h^φ)^{φ⁻¹} = h by the chain rule.

The audit's fifteen non-gap rows also included the Ding–Gwynne Prop 1.9 step. The graph review reinstated that step as a minor gap, and it is listed above.

### Errata

These lists follow the independent gap audit. The identifiers E-P1 to E-P19 number the manuscript's errata.

#### The manuscript (revised draft of October 1, 2026)

*Main.*

- **E-P1. Lemma 3.1 (l. 163–167), statement.** The hypotheses are ill-posed: arbitrary generalized functions, and couplings that do not carry the corrections. “Jointly with the fields” is false on a larger neighbourhood (g_n = g + ψ). The proof (l. 169–170) also needs one common locality functional.
- **E-P2. Lemma 4.1 (l. 275–278), proof.** The connector pays only up to radius s_j, while the loop may lie near √s_j. Two-scale repair; the statement is unchanged.
- **E-P3. Lemma 2.1 (l. 139–144), proof.** The loop chaining inherits the gaps of Pfeffer's Lemma 2.26: connectivity, and an unpaid terminal loop.
- **E-P4. Prop 6.1 (l. 471–479, 494–496), proof.** Endpoint exclusion. Retain index j only if P(0), P(T) ∉ B_{2r_j}(z_j), using a last-exit/first-entry corridor.
- **E-P5. Lemma 3.3 (l. 218–236), proof.** The varying laws need one Borel locality functional (also at l. 233). The barrier transfer needs a margin event that is stable under the non-constant Weyl correction and Borel-local.
- **E-P6. Universal locality (l. 169–170, 233).** Comparing fields of different laws through “determined by” needs a common functional (coin mixture).
- **E-P7. (G1) and (G3) (l. 383–395, 400–401).** They inherit the two gaps in Ding–Gwynne's proof of Lemma 3.14 listed below. Repaired by the sealed two-scale ratio and closed-endpoint estimates.

*Minor.*

- **E-P8. Lemma 1.2 (l. 83–87).** The uniform limit must be shown to be a metric curve.
- **E-P9. Lemma 4.2 (l. 302–322).** The parameter space is not shown to be Polish; use a standard Borel space. The compact annulus must contain the test balls and annuli of (8). Condition (7) is field data; read it as d(u, v) ≤ M.
- **E-P10. Lemma 5.1 (l. 416–417).** Read “the field near the *closed* annulus”. The event is universally measurable, not Borel.
- **E-P11. Prop 4.3 (l. 344–366).** The Skorokhod state space, the marks and the universally measurable transfer are unstated. So is the application of Lemma 3.3 to the varying zoomed fields.
- **E-P12. Lemma 7.1 (l. 524–533).** The couplings need an extension of the probability space. The pathwise transfer needs the Weyl length formula.
- **E-P13. Closure of the field class under conformal pullback (l. 26, 37, 544–545).** It is used implicitly; it is proved for Greenian U, V.
- **E-P14. Domain forms of (I1) (l. 47–48).** The cited results are stated for whole-plane fields only; the domain forms are derived through realizations.
- **E-P15. Lemma 2.1 (l. 124–125, 131–136).** The law of the log-normal factor depends on n; only tightness holds, and only tightness is used. Bound (4) is applied at centres near K, not in K.

*Citation slips.*

- **E-P16.** l. 51: Pfeffer's Props 1.10 and 1.12 are in his §1.2, not §1.3.
- **E-P17.** l. 290: θ is the exponent of DG Lemma 2.13 (§2.6), not of “Section 3.2”.
- **E-P18.** l. 140 and 182–183: [2, Lemma 2.26] and [1, Lemma 2.11] are used for their proofs, in variants. The “half the cost” event at l. 183–184 is a stronger variant, and still valid.
- **E-P19.** l. 52–53: Euclidean continuity of finite-length paths is attributed to Pfeffer, whose printed proofs presuppose it. The escape-barrier route supplies it.

`SG-CC-REV-001` and the reading notes above are not errata.

#### The cited literature

**Gwynne–Miller, arXiv:1905.00384v2.**

- **GM-L24-N1 (false printed statement; the most serious literature erratum).** Gwynne–Miller fix a smooth, compactly supported, radially symmetric bump function 𝐟 with ∫𝐟 = 1. They set h_{𝐟,r}(z) := (h(r · + z), 𝐟) in their (2.1), and they normalize the whole-plane GFF by h_{𝐟,1}(0) = 0. In Lemma 2.4 the maps satisfy φ_n(0) = 0 and φ_n′(0) → 1/α. For every compact K, display (2.6) (TeX l. 519–520) claims

  (h ∘ φ_n⁻¹ − (h ∘ φ_n⁻¹)_{𝐟,|α|}(0))|_K → h(α ·)|_K in total variation.

  The proof asserts (l. 549) that h(α ·) is normalized so that (h(α ·))_{𝐟,|α|}(0) = 0, and it uses this again in (2.8) (l. 552–553). Since 𝐟 is radial, (h(α ·))_{𝐟,s}(0) = h_{𝐟,s|α|}(0), so (h(α ·))_{𝐟,|α|}(0) = h_{𝐟,|α|²}(0). Now take K containing the support of |α|⁻²𝐟(·/|α|) and pair both sides with that test function. The left side of (2.6) gives 0 identically. The right side gives h_{𝐟,|α|²}(0) − h_{𝐟,1}(0), a non-degenerate centred Gaussian when |α| ≠ 1. So the total-variation distance is 1 for every n, and (2.6) and (2.8) are false as printed whenever |α| ≠ 1.

  **Correction:** replace the scale |α| by |α|⁻¹ in (2.6) and (2.8). Then (h(α ·))_{𝐟,|α|⁻¹}(0) = h_{𝐟,1}(0) = 0, and the printed argument goes through. The supercritical manuscript already uses the corrected scale. In its Lemma 3.3 (l. 213), f_a(w) = |a|⁻² 𝐟(w/a) with a = α⁻¹ is the smooth average at scale |a| = |α|⁻¹. Gwynne–Miller's own later use (TeX l. 583–590) needs only the convergence of the constants, which (2.5) gives at either scale. The formal route of input (I4) uses the corrected statement.
- **Typos in Lemma 2.4's proof.** At l. 539, f(α ·) should read f(α⁻¹ ·). At l. 548, φ(U_n) should read φ_n(U_n).
- **Lemma 2.4's proof, other gaps.** Lemma 2.3 allows U_n = ℂ, where no zero-boundary GFF exists; use disks. With (h, 𝐟) = 0 the Markov parts are not independent; recentre. The energy decay of the harmonic part does not follow from the cited sup estimate of IG4. The cut-off energy needs an L² bound. The Cameron–Martin shift is random, so the total variation is bounded through a mixture: TV ≤ E min(1, √(e^{E(S)} − 1)).
- **l. 313.** The Markov decomposition h|_U = h̊^U + 𝔥^U “for each deterministic open set U” tacitly requires a Greenian U.
- **l. 319–320 and 362.** The domain axioms and pullback locality are asserted “by inspection” and as “easily seen”.
- **Theorem 1.3 (l. 327)** prints φ : ℂ → U; it should read φ : U → φ(U). This slip is not consumed.

**Ding–Gwynne, arXiv:2110.00177v3.** The repairs of both main items are proved in the sealed `SupercriticalLQGUniqueness` formalization.

- **Lemma 3.14 proof (l. 1976).** The first clause of the good-annulus event is a ratio, around ≤ δ^θ · across. It does not follow from Lemma 2.13, which bounds around-distances by δ^θ times the elapsed geodesic time. The repair is a two-scale ratio estimate.
- **Lemma 3.14 proof (l. 1979–1984).** Lemma 2.14 needs geodesic endpoints in the open set, away from the curve η. It is applied to geodesics with boundary endpoints. The printed “∂B_r” endpoint is a typo: it lies on η itself. The repair is a closed-endpoint extension, after which α → 1.
- **Prop 1.9 proof (l. 499–501), minor.** The proof needs P[D_h(0, ∂𝔻) < ∞] > 0, which is unstated. It follows from Pfeffer's Prop 1.11(b).

**Pfeffer, arXiv:2104.04020v3.**

- **Lemma 2.26 proof (l. 1590–1611).** The union of the chained loops need not be connected, and the terminal loop is unpaid.
- **Props 1.10 and 1.12.** The printed proofs presuppose that paths of finite metric length are Euclidean continuous. The escape-barrier repair is proved in `SupercriticalLQGUniqueness`.

**Miller–Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2.**

- **Prop 2.10 proof (l. 1174).** The harmonic variance bound is asserted without proof and without uniformity over the observation circle. Repaired by nested disks, which give the bound −log(1 − |y|²/L²).
- Prop 2.8 is stated for bounded W only. This is a scope remark, not an error.

## About the source files

The ten frozen files are copied byte for byte from the sealed development commit recorded in `source-manifest.json`; see [Immutable frozen comments](#immutable-frozen-comments). The proof body of each frozen theorem is `by exact` its provider theorem.

The other 252 files keep their mathematical documentation: module docs, docstrings and comments are shipped. Only references to the development process were edited, line by line: the provenance line at the top of each landed file was dropped; work-item labels, private paths and the names of unlanded development files were removed or replaced by what they stood for; internal gap identifiers were replaced by the gap labels of this guide; and a few progress remarks that are no longer true were corrected. Three of these corrections (in `Good/Assembly.lean`, `Good/Probability.lean` and `GM24/Main.lean`) replace whole stale passages by reviewed text that names the declarations discharging the inputs; the development files themselves keep the sealed bytes. A comment line without such a reference is unchanged, and no module doc or docstring was removed. One Lean name changed: the released `SupercriticalLQGUniqueness` gave a development namespace of its two-scale events the public name `S36Events.CoveredStep`, and the eight uses in `Improve/Improvement.lean` follow it (the scrub checks that each renamed lemma exists in the released library). Every other Lean code token is unchanged. Each edited file's manifest row records both the development hash and the shipped hash.

Module paths and internal declaration names otherwise keep their development names. Some carry development labels, for example `P43Final`, `GM24`, `BiLip.L51`, `Lemma51LocalInput`, `prop43_input_slot`, the working copies `BiLip.Cand`, `Domain.Cand` and `Root.Cand` of the statement candidates, and version suffixes; they have no mathematical meaning. Named propositions such as `Prop43Input` or `Lemma51LocalInput` are statements proved inside the library; none is an assumption of the frozen theorems. The public claims are exactly the two frozen theorems and the supporting theorems listed in the status table and in `Check.lean`.

The public frozen manifest is a metadata projection: it replaces private approval-record paths with dates and request hashes, and its source field states the line-number conventions of this guide. `manifest-provenance.json` records the SHA-256 of the authoritative development manifest and of each key-2 seal audit.

## Reproduce the checks

The pinned toolchain is `leanprover/lean4:v4.34.0-rc2`; Mathlib is `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`. The included `lake-manifest.json` fixes the other dependencies. From the root of `leobon12/lean-formalizations`, with elan, Lake, Python 3 and the pinned dependencies available:

```sh
lake exe cache get
lake build SupercriticalConformalCovariance.Frozen.ConformalCovariance \
  SupercriticalConformalCovariance.Frozen.DomainMetric_ae_eq_of_isDomainRealization \
  SupercriticalConformalCovariance.Root.AllXi SupercriticalConformalCovariance.GMForm.Base
python3 -I results/supercritical-conformal-covariance/check_release.py
python3 -I scripts/verify.py --scan-only
lake env lean results/supercritical-conformal-covariance/Check.lean
```

`Check.lean` runs `assert_no_sorry` and `#print axioms` on each advertised theorem. Every reported axiom must be one of `propext`, `Classical.choice` and `Quot.sound`. `Check.lean` also checks that the all-ξ theorem implies the frozen Theorem 1.1. `check_release.py` checks the frozen files against the hashes, declarations and split policy of the frozen-anchor manifest, and the hash of the shipped text extraction. `scripts/verify.py --scan-only` checks the selected module closure, source hashes, import closure and forbidden proof tokens. `lake env leanchecker --fresh` can replay each frozen theorem module independently.

The import closure of the shipped files has 4,023 modules: the 262 files of this library and 3,761 modules of already released libraries (see [What is in the library](#what-is-in-the-library)). These upstream results are proved in their libraries, not assumed as new axioms.

## Credits and citation

The manuscript is an AI-generated, unrefereed draft in `leobon12/ai-generated-mathematics`; cite it by that repository, the file `papers/supercritical-conformal-covariance.pdf` and the commit `51d7c1283`. Cite the Lean source snapshot by repository URL and release commit. The development modules had no file-level author or copyright notices. The manuscript's pinned text extraction is included under `source/` so that line references can be checked; the PDF is linked at its pinned revision, not copied. The manuscript is the author's own AI-generated paper. The statements were frozen and audited following Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) workflow.

[All released formalizations](../../README.md)
