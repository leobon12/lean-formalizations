# Almost sure convergence of supercritical Liouville first passage percolation

**Status.** Theorem 1.1 is `PROVED` in Lean with no assumptions: both frozen theorems are sealed with two keys, and every advertised theorem depends only on Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`.

This Lean 4 project formalizes Theorem 1.1 of *Almost sure convergence of supercritical Liouville first passage percolation*, a research manuscript dated October 1, 2026 (14 pp.), an **AI-generated, unrefereed draft**: [PDF](https://leobon12.github.io/papers/lqg-2026-10-25/almost-sure-supercritical-lfpp.pdf) (SHA-256 `98dd76951e78d90388faeea14e039d93de054504572042c588988124af229c9f`). The PDF is not copied here, but its plain-text extraction is: [source/almost-sure-supercritical-lfpp.txt](source/almost-sure-supercritical-lfpp.txt) (SHA-256 `05f315d03db056d70a4af93f8300040daeddbc9a4509faec4cbf366d89dbe6e0`). Line numbers “l. N” of the manuscript, here and in the Lean files, are lines of that file. References [1]–[6] are those of the manuscript: [1] Ding–Gwynne, *Uniqueness of the critical and supercritical LQG metrics* (arXiv:2110.00177); [2] Ding–Gwynne, *Up-to-constants comparison of LFPP and LQG* (arXiv:2108.12060); [3] Ding–Gwynne, *Regularity and confluence of geodesics for the supercritical LQG metric* (arXiv:2104.06502); [4] Pfeffer, *Weak LQG metrics with matter central charge c ∈ (−∞, 25)* (arXiv:2104.04020); [6] Ding–Gwynne, *Tightness of supercritical LFPP* (arXiv:2005.13576).

In words: let h be a whole-plane Gaussian free field normalized by h₁(0) = 0, fix ξ > ξ_crit, let 𝔞_ε be the median of the left–right crossing distance of [0,1]² for heat-kernel LFPP D_h^ε with cutoff ε, and let D_h be the limit in probability of 𝔞_ε⁻¹ D_h^ε constructed by Ding–Gwynne [1, Theorems 1.3 and 1.8]. Then, on one event of probability one, 𝔞_ε⁻¹ D_h^ε → D_h as ε → 0 **through all positive real cutoffs**, in the topology on lower semicontinuous functions on ℂ × ℂ: the lower-limit inequality (1.2) holds along every convergent sequence of endpoint pairs, and every pair has a recovery sequence; infinite distances are allowed.

| Result | Lean declaration | Status |
| --- | --- | --- |
| Theorem 1.1 | `SupercriticalLFPPAS.lfpp_ae_lscTendsto` (frozen) | **PROVED** (two keys). Key 1: the seal, development commit `8d3cea093` (the frozen body became `by exact SupercriticalLFPPAS.Implementation.lfpp_ae_lscTendsto_impl`; frozen-anchor checker, unchanged statement hash, standard axioms, `leanchecker --fresh` kernel replay). Key 2: an independent seal audit, `VERDICT: PASS`, development commit `44e1b3bfb`, with a second fresh kernel replay |
| Existence of jointly continuous heat versions | `SupercriticalLFPPAS.exists_jointHeatVersion` (frozen) | **PROVED** (two keys). Key 1: sealed at the freeze, development commit `70c6b99de`. Key 2: an independent seal audit, `VERDICT: PASS`, development commit `380d655dd` |
| Theorem 1.1 for every ξ > 0 | `SupercriticalLFPPAS.Assembly.lfpp_ae_lscTendsto_allXi` | Supporting theorem: the same proof without the hypothesis ξ > ξ_crit; not frozen, not sealed; audited by `Check.lean` |
| Uniqueness of jointly continuous heat versions | `SupercriticalLFPPAS.ae_eq_of_jointHeatVersions` | Supporting theorem, proved; not frozen |
| Existence, pathwise form | `SupercriticalLFPPAS.Implementation.exists_jointHeatVersion_pathwise` | Supporting theorem, proved (the lemma behind the frozen existence theorem) |
| The statement without joint continuity is false | `SupercriticalLFPPAS.RefutedV1.not_thm11v1` | Supporting theorem, proved |

## Exact frozen statements

The declaration heads below are copied from the frozen files. The proof bodies are omitted; each is `by exact` its provider theorem, which has exactly the same statement. The quantifier order is part of the statement.

```lean
theorem lfpp_ae_lscTendsto :
    ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) →
      ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
          (∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2) →
        ∀ L : Ω → LSCMetric,
          LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
            (fun ω => (L ω).toLSCFun.1) →
          ∀ᵐ ω ∂P, ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
            LSCTendsto (fun n => rescaledLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω)) (L ω).toLSCFun.1 :=
```

```lean
theorem exists_jointHeatVersion :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
        ∃ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) ∧
          ∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2 :=
```

The definitions in these statements are frozen definitions of already released libraries, imported unchanged (besides Mathlib, and `DistC`, the distributions on ℂ, from the released `LQGMetric`): `IsNormalizedWholePlaneGFF`, `IsHeatSmoothing`, `IsLFPPNormalizer`, `rescaledLFPP`, `LSCMetric` and `toLSCFun`, `LSCTendsto` and `LSCTendstoInProbability` from [`SupercriticalLQGUniqueness`](../supercritical-lqg-uniqueness/), and `xiCrit` from [`SupercriticalConformalCovariance`](../supercritical-conformal-covariance/). In words:

- `IsNormalizedWholePlaneGFF h P`: h is a whole-plane GFF on (Ω, P) whose circle average over ∂B₁(0) is 0 almost surely.
- `IsHeatSmoothing P h ε (X ε)`: X ε is a continuous version of h*_ε = h ∗ p_{ε²/2}, with p_t(z) = (2πt)⁻¹ e^{−|z|²/(2t)} (for each ε and z, almost surely the pairings of h with p_{ε²/2}(z − ·) times exhausting cutoffs converge to X ε ω z).
- `IsLFPPNormalizer ξ ε (m ε)`: m ε is the median of the left–right crossing distance of [0,1]² by piecewise C¹ paths in the square, for every normalized GFF and every heat version; it is unique (the released `existsUnique_isLFPPNormalizer`).
- `rescaledLFPP ξ a φ` is a⁻¹ times the LFPP distance inf_P ∫₀¹ e^{ξ φ(P(t))} |P′(t)| dt over piecewise C¹ paths, in [0, ∞].
- `LSCTendsto F f`: (1.2), f(z, w) ≤ liminf F_n(z_n, w_n) whenever (z_n, w_n) → (z, w), and recovery, every (z, w) has (z_n, w_n) → (z, w) with F_n(z_n, w_n) → f(z, w), with values in [−∞, ∞] ([1, Definition 1.2]). `LSCTendstoInProbability`: every sequence of cutoffs tending to 0 has a subsequence along which `LSCTendsto` holds almost surely.
- `xiCrit` is the infimum of the ξ > 0 whose LFPP exponent Q(ξ) is 2 ([1, (1.7)]).

## How the statement differs from the printed theorem

The independent statement audit of the frozen surface (below) approved it with these disclosures.

1. **Joint continuity of the heat versions (the one correction).** Each h*_ε is determined by h only up to a null set that depends on ε, and Theorem 1.1 is an almost sure statement about uncountably many cutoffs at once. Read with arbitrary versions chosen separately for each ε, the printed statement is **false**: on a product space, changing the versions on countably many cutoffs that depend on an independent uniform variable keeps every version a version and keeps the limit in probability, yet sends the rescaled distance from 0 to 1 to 0 along a random sequence of cutoffs, which contradicts (1.2) at every sample. `RefutedV1.not_thm11v1` proves this in Lean; `RefutedV1.Thm11v1` is that reading. The frozen theorem therefore quantifies over families X of continuous heat versions that are, almost surely, jointly continuous in (ε, z). This is the paper's own object: the proof differentiates the realization-wise convolution in the cutoff (l. 164) and interpolates between cutoffs on one event. Such families exist (the frozen `exists_jointHeatVersion`, and in pathwise form `Implementation.exists_jointHeatVersion_pathwise`: on one event the convolution exists at every (ε, z) and is jointly continuous), and any two agree almost surely at every ε at once (`ae_eq_of_jointHeatVersions`). So the class of admissible X is, up to one null set, exactly the realization-wise convolution h ∗ p_{ε²/2}. The theorem holds for every such family, which is stronger than for one chosen family.
2. **The limit.** D_h enters as any `L` such that the rescaled LFPP converges to `L` in probability in the lower semicontinuous topology. Such an `L` exists (the released `lfpp_tendstoInProbability`) and is unique almost surely, so “for every such L” is the paper's D_h. `L` need not be measurable, which makes the statement stronger.
3. **The critical parameter.** The hypothesis `xiCrit < ξ` is the printed one. Lean's convention `sInf ∅ = 0` could only weaken it. The proof never uses it; see [Theorem 1.1 for every ξ > 0](#theorem-11-for-every-ξ--0).
4. **Probability spaces.** Ω ranges over `Type` (the lowest universe), the convention of every released theorem of `SupercriticalLQGUniqueness`.
5. **Measurability.** Neither X nor L is required to be measurable, and joint continuity is required only almost surely (equivalent to everywhere, after a modification on a null set). Both choices make the statement more general.
6. **“Through all positive real values.”** The conclusion holds on one probability-one event for every sequence of positive cutoffs tending to 0, chosen after the sample: the sequential form of the limit ε → 0 through the positive reals.
7. **The normalizer.** The theorem holds for every family `m` of medians; by uniqueness this is the paper's 𝔞_ε.

## Theorem 1.1 for every ξ > 0

`SupercriticalLFPPAS.Assembly.lfpp_ae_lscTendsto_allXi` (module `Assembly.AllXi`) is Theorem 1.1 without the hypothesis ξ > ξ_crit: the same conclusion for **every** ξ > 0. The imported results (i)–(v) hold for every ξ > 0, and no step of the proof uses ξ > ξ_crit. The provider of the frozen theorem applies exactly this proof and discards the hypothesis. `Check.lean` checks that the all-ξ theorem implies the frozen one and that the frozen type is, by `rfl`, `∀ ξ, xiCrit < ξ →` its type at ξ. The all-ξ theorem is not frozen and not sealed. No statement is made simultaneously for all ξ on one event, and the paper makes none.

## The imported results are proved, not assumed

The manuscript imports five groups of results (l. 72–113). Each is a released theorem or is proved in this library from released theorems; none is a hypothesis.

| Manuscript input | How it is obtained |
| --- | --- |
| (i) convergence in probability, the strong metric, Weyl scaling, locality, the scaling relation (1.3) [1, Theorems 1.3, 1.8, Definition 1.7] | released `SupercriticalLQGUniqueness` theorems `lfpp_tendstoInProbability` and `exists_strongLQGMetric_lfppLimit` (the LFPP limit is a strong LQG metric, also for a GFF plus a bounded continuous function); (1.3) is proved here from coordinate change and Weyl scaling by a random constant (`Scaling.scalingD_holds`) |
| (ii) geodesics, Euclidean regularity, escape (1.4) [4, Propositions 1.10, 1.12, Lemma 3.12] | `Inputs.ae_exists_pointGeodesic_of_finite` (from the released proof of [4, Proposition 1.12] for weak LQG metrics), `Inputs.ae_strongLQGMetric_euclideanRegularity` (a compact-uniform modulus derived from lower semicontinuity replaces the Hölder bound of [4, Proposition 1.10], which is not needed) and `ae_d2EscapeSetDist_tendsto` (from the barrier property) |
| (iii) rational-circle distances (1.5) [4, Theorem 1.7] | `rationalCircleDistance_tendstoInMeasure`, from the released proof of [4, Theorem 1.7] and uniqueness of limits; circles of positive radius |
| (iv) localized comparison, scaling ratios, annular tightness [2, Proposition 3.6, Lemma 3.7, Theorem 1.9, Lemma 3.1], [6, Proposition 4.1] | the released polylogarithmic route `SupercriticalLQGUniqueness.B2.Polylog` (localized comparison at q = 1, `PLRatioUniform`, `PLHeatAnnulusTight`), whose Ding–Gwynne inputs are proved in `SupercriticalLQGUniqueness.B2.Final`; a strong metric is a weak metric in the sense of [4] with scaling constants exactly r^{ξQ} (`Compare.isPfeWeakMetric_of_isStrongLQGMetric`), so [2, Theorem 1.9] is not needed |
| (v) annulus concentration (1.6) [3, Lemma 2.12] | `Concentration.paper_annulus_concentration` and `Concentration.paper_annulus_concentration_arbitrary_rate`, from Gwynne–Miller's local-metrics Lemma 3.1 (`LQGMetric.LM.lmLem3_1a`) by an off-centre transfer, with the exact separation and σ-algebra hypotheses |

## Corrections to the printed proof

Three refute-first audits of the manuscript's proof (Sections 1–3 with the imported results; Sections 3–7; an independent cross-check of Sections 3–7) found no false statement besides the version issue above. The Lean proof repairs these gaps and imprecisions; none changes the theorem:

- (6.1) of Lemma 6.1 lacks an absolute value and fixes one endpoint; the proof needs the symmetric two-point form sup over ε, δ in [(n+1)^{−a}, n^{−a}] of |log(𝔞_ε/𝔞_δ)| → 0, which the same argument gives (`Normalizer.normalizerWindow_of`).
- Lemma 4.1, last paragraph (l. 466–468): the case C₀ ≥ K must be split at C₀ = (1 + d₀)K; the conclusion (4.1) is unchanged.
- Lemma 6.2: the mesh exponent must depend on the radius, since the failure rate of [2, Proposition 3.6] does.
- §7: the probability-one event must also contain the geodesic event and the Euclidean regularity of D_h.
- Lemma 2.1, (2.2): only the heat kernel is differentiated in the cutoff, with an explicit rate; the differentiability of δ ↦ h*_δ is not needed.
- Lemma 2.2: the probability that a path of length at most M from K exits B_R(0), which is not obviously an event, is bounded through a measurable larger event; Remark 3.3's measurability sketch is replaced by a proof (universally measurable projections, countable infima, locality).
- Input (iii) is used for circles of positive radius, where finiteness of the distance follows from Axiom V; input (v) is used in the precise form of [3, Lemma 2.12].
- The interfaces of the proof add the hypotheses the printed arguments use silently: Lemma 3.4 states exactly the hypotheses it uses, Lemma 3.5 fixes its quantifier order and constants uniformly over probability spaces, and Lemma 4.1 measures target distances inside a bounded convex set containing B_{R+1}(0).

## What is in the library

The library `SupercriticalLFPPAS` ships 103 Lean files (23,603 lines, 19,747 of them code), the import closure of the two frozen theorems and of the supporting theorems; the aggregator `SupercriticalLFPPAS.lean` and seven unused modules are not shipped.

| Part of the manuscript | Directories | Modules |
| --- | --- | ---: |
| §§1–2: the scaling relation (1.3), field estimates (Lemma 2.1), dilation (2.4), the localized comparison, annulus concentration, annular tightness, LFPP geodesics | `Field`, `Scaling`, `Compare`, `Concentration`, `Tightness`, `Geodesic` | 17 |
| §3: Lemmas 3.1–3.5, separating paths, good root scales, deterministic tools | `Local`, `Separating`, `GoodRoot`, `Det` | 29 |
| §4: Lemma 4.1 and the contraction step | `Contraction`, `ContractionStep` | 18 |
| §5: Proposition 5.1 and the identification of the constant | `Proposition51`, `Identification`, `Iteration` | 9 |
| §6: Lemmas 6.1 and 6.2 | `Normalizer`, `Escape` | 3 |
| §7: the probability-one event and Theorem 1.1 | `Main` | 5 |
| Imported-result adapters, interface statements, assembly | `Inputs`, `Core`, `Assembly` | 17 |
| Frozen statements and their providers; supporting theorems on heat versions | `Frozen`, `Implementation` | 5 |

The proof is organized through named interface statements (`Core.*Stmt` in `Core/Interfaces.lean`); each is proved in the library, and `Assembly.mainAe_holds_of_window` composes them. None occurs in a frozen statement, and none is an assumption of the advertised theorems.

The proof also uses these already released libraries, unchanged (4,972 modules of their import closure): `SupercriticalLQGUniqueness` and its top-level support modules (2,722), `LQGMetric` (1,392), `QuantumZipper` (746), `LQGDimension` (107), `HigherDimLQGMetric` (4) and `SupercriticalConformalCovariance` (1, the definition `xiCrit`).

## How it was checked

The project follows Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) workflow.

1. **Statement.** A first statement draft was found false (disclosure 1); the corrected draft and the existence theorem passed an independent statement audit (binders classified against l. 21–51: no excess hypothesis; joint continuity justified as above; every definition unfolded and checked against the manuscript and [1]; junk values checked), were approved under the author's delegation, and were frozen in one-declaration files whose bytes and elaborated types are pinned by a hash manifest, together with every upstream module they import.
2. **Proof.** Each frozen theorem has a provider theorem with exactly the frozen statement. The provider of Theorem 1.1 composes the interface statements; Lemma 6.1 is the last one discharged.
3. **Two-key seals.** A theorem is `PROVED` only after both keys. *Key 1:* only the frozen body changes, to `by exact <provider>`; the frozen-anchor checker, the build, an unchanged statement hash and `#print axioms` must pass, and for Theorem 1.1 a fresh kernel replay (`leanchecker --fresh`) of both frozen modules. *Key 2:* a fresh auditor, who did no earlier work on the theorem, rechecks the statement against the manuscript, reads the provider chain for hypotheses that encode proof steps, checks the axioms and replays the kernel check. Both key-2 audits returned `VERDICT: PASS`.
4. **Release checks**, on the staged public tree (development commit `04dc90bf4`, unchanged, on the public `main`): every new module and every released module that depends on the comment-stripped public sources of `SupercriticalLQGUniqueness` (the 103 files of this library; that library, its support modules and `xiCrit`: 2,723 modules) was compiled from empty project artifacts, against 2,249 released modules whose oleans are trace-linked to the public bytes; `Check.lean` reports only `propext`, `Classical.choice` and `Quot.sound` for each of the 6 advertised theorems; the certificate's whole-library axiom walk, restricted to this library, reaches only these three axioms from all 1,644 declarations; the two frozen statements, elaborated against the public sources, have exactly their sealed statement hashes; the public source scan passes.

## Comments in the source files

The two frozen files ship byte for byte as sealed, so their comments are unchanged. They cite development records that are not part of this release: the rulings P6 and P7 (P6 is disclosure 1; P7 approved the frozen statements under the statement audit's conditions), the statement audit and its notes N1–N5 and conditions C1–C5 (summarized above: N1 is disclosure 3, N2 disclosure 4, N3 the disclosure of the version hypothesis, N4 marks the first draft's notes as superseded, N5 is disclosure 2; C1–C5 require freezing the corrected draft together with the existence theorem, counting Theorem 1.1 as proved only after both are sealed, providing the uniqueness theorem and keeping the refutation of the first draft, and pinning the upstream definitions), the manuscript PDF (linked above), the frozen manifest and the statement draft. Their wording “`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED`” describes the two states the manifest allows; both theorems are `SEALED`, as the status table says.

Comments in the other modules also cite internal development records (the planning audits of Sections 1–3 and 3–7, work-package labels, and rulings P8–P9 on the interface plan). These records are not part of the release; the Lean statements and proofs do not depend on them. Module paths and internal declaration names keep their development names; names such as `d1_lemma_3_4` or `Lemma41Stmt` carry no mathematical claim beyond their Lean statements. The public claims are exactly the theorems in the status table, all audited by [`Check.lean`](Check.lean).

## Reproduce the checks

The pinned toolchain is `leanprover/lean4:v4.34.0-rc2` and Mathlib is `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`; the included `lake-manifest.json` fixes the other dependencies. From the root of `leobon12/lean-formalizations`, with elan, Lake and Python 3:

```sh
lake exe cache get
lake build SupercriticalLFPPAS.Frozen.Lfpp_ae_lscTendsto SupercriticalLFPPAS.Frozen.Exists_jointHeatVersion \
  SupercriticalLFPPAS.Assembly.AllXi SupercriticalLFPPAS.Implementation.JointHeatVersion
lake env lean results/almost-sure-supercritical-lfpp/Check.lean
python3 -I scripts/verify.py --scan-only
lake env leanchecker --fresh SupercriticalLFPPAS.Frozen.Lfpp_ae_lscTendsto
```

`Check.lean` runs `assert_no_sorry` and `#print axioms` on each advertised theorem; every reported axiom must be one of `propext`, `Classical.choice` and `Quot.sound`. It also checks that the all-ξ theorem implies the frozen Theorem 1.1 and that the refuted reading would imply it. `scripts/verify.py --scan-only` checks the selected module closure, source hashes, import closure and forbidden proof tokens; the repository's [certificate](../../Certificate.lean) audits the same theorems and every constant of the library. `leanchecker --fresh` replays a frozen module in an independent kernel.

## Credits

The manuscript is the author's AI-generated, unrefereed paper; cite it by its title, date and the PDF above. Cite the Lean source snapshot by repository URL and release commit. The mathematical results it builds on are due to the authors of the cited works; the released libraries listed above formalize them. The development files had no file-level author or copyright notices.

[All released formalizations](../../README.md)
