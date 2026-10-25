# Critical and supercritical Liouville quantum gravity metrics: convergence, existence and uniqueness

This Lean 4 library formalizes the main results of Jian Ding and Ewain Gwynne, *Uniqueness of the critical and supercritical Liouville quantum gravity metrics*, [arXiv:2110.00177v3](https://arxiv.org/abs/2110.00177v3) (2022; *Proceedings of the London Mathematical Society*, 2023), for every parameter ξ > 0:

- **Theorem 1.3.** For a whole-plane GFF plus a bounded continuous function, the re-scaled Liouville first passage percolation (LFPP) metrics 𝔞_ε⁻¹ D^ε_h converge in probability, for the topology on lower semicontinuous functions on ℂ × ℂ, to a random lower semicontinuous metric on ℂ that may take the value ∞.
- **Theorem 1.8.** (i) There is a strong LQG metric D with parameter ξ such that the limit of Theorem 1.3 is almost surely D_h. (ii) Two strong LQG metrics with parameter ξ differ almost surely by a deterministic positive factor.
- **Theorem 1.13.** Two weak LQG metrics with parameter ξ (Definition 1.12) differ almost surely by a deterministic positive factor.
- **Equations (1.4) and (1.5).** The LFPP median normalizer 𝔞_ε and the LFPP distance exponent Q = Q(ξ) are well defined: each is the unique value with its defining property.

Every result is proved, with no assumption. The paper's literature inputs — the tightness and subsequential-limit theory of Ding–Gwynne's supercritical LFPP paper, Pfeffer's Theorem 1.7, Theorem 1.9 of Ding–Gwynne's up-to-constants comparison and the positivity of the distance exponent by Ding–Gwynne–Sepúlveda — are proved here, in the form the proof uses (see *How Theorems 1.3 and 1.8(i) are proved*).

Each theorem is certified by a sealed frozen declaration together with the frozen theorems for its constants:

| Paper result | Frozen theorems |
| --- | --- |
| Theorem 1.3 | `lfpp_tendstoInProbability` with `existsUnique_isLFPPNormalizer` |
| Theorem 1.8(i) | `exists_strongLQGMetric_lfppLimit` with `existsUnique_isLFPPExponent` and `existsUnique_isLFPPNormalizer` |
| Theorem 1.8(ii) | `strongLQGMetric_unique` with `existsUnique_isLFPPExponent` |
| Theorem 1.13 | `weakLQGMetric_unique` with `existsUnique_isLFPPExponent` |
| Equation (1.4) | `existsUnique_isLFPPNormalizer` |
| Equation (1.5) | `existsUnique_isLFPPExponent` |

The statements characterize Q and 𝔞_ε by predicates (`IsLFPPExponent`, `IsLFPPNormalizer`), so a theorem about "the" exponent or normalizer is the theorem for every value with the defining property, together with the existence and uniqueness of that value.

## Frozen theorem statements

The following are the exact declaration heads, copied from the author-approved frozen files. The definitions they mention are in [`SupercriticalLQGUniqueness/Frozen/`](../../SupercriticalLQGUniqueness/Frozen/). The statements retain the paper's probability quantifiers and almost-sure event order.

### Equation (1.5): exponent well-definedness

```lean
theorem existsUnique_isLFPPExponent :
    ∀ ξ : Set.Ioi (0 : ℝ), ∃! Q : ℝ, IsLFPPExponent ξ Q :=
```

### Equation (1.4): normalizer well-definedness

```lean
theorem existsUnique_isLFPPNormalizer :
    ∀ ξ ε : Set.Ioi (0 : ℝ), ∃! a : Set.Ioi (0 : ℝ), IsLFPPNormalizer ξ ε a :=
```

### Theorem 1.3: convergence of LFPP

```lean
theorem lfpp_tendstoInProbability :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        ∃ L : Ω → LSCMetric, Measurable L ∧
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (L ω).toLSCFun.1) :=
```

### Theorem 1.8(i): existence of the strong metric as the LFPP limit

```lean
theorem exists_strongLQGMetric_lfppLimit :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∃ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D ∧
        ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (D (h ω)).toLSCFun.1) :=
```

### Theorem 1.8(ii): strong metric uniqueness

```lean
theorem strongLQGMetric_unique :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsStrongLQGMetric ξ Q D → IsStrongLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D' (h ω)).1 (u, v) = ENNReal.ofReal C * (D (h ω)).1 (u, v) :=
```

### Theorem 1.13: weak metric uniqueness

```lean
theorem weakLQGMetric_unique :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) :=
```

## Statement conventions

The labels below are those of the decision records behind the frozen statements; each convention is stated in full here.

- **A9: predicate form.** `IsLFPPExponent ξ Q` states the characterization of Q in (1.5), and `IsLFPPNormalizer ξ ε a` states that a is a median of the LFPP left–right crossing distance of the unit square in (1.4). The well-definedness theorems give existence and uniqueness, so each theorem that takes such a value is the paper's theorem for the paper's value. The order of the factor in Theorem 1.8(ii) follows the second sentence of the paper's Theorem 1.8.
- **A10: positivity of Q is not part of the exponent statement.** The exponent theorem asserts existence and uniqueness only. The proofs prove Q > 0 where they use it (in Theorem 1.13 from the weak metric axioms; in Theorems 1.3 and 1.8(i) from the LFPP estimates, see below).
- **A22: readings of Theorems 1.3 and 1.8.**
  - *Fields and heat versions.* h is a whole-plane GFF plus a bounded continuous function (`IsGFFPlusBddCont`), as in Theorems 1.3 and 1.8(i); the uniqueness clauses keep the paper's "plus a continuous function" (`IsGFFPlusCont`). LFPP is computed from a continuous version X ε of the heat-kernel mollification h*_ε of (1.2) (`IsHeatSmoothing`). The theorems hold for every family of such versions; none is chosen.
  - *The normalizer.* The median predicate in (1.4) quantifies over every probability space carrying a normalized whole-plane GFF and every continuous heat version, so 𝔞_ε does not depend on a chosen realization. Its values are positive reals.
  - *One limit per law in Theorem 1.3, one metric in Theorem 1.8(i).* In Theorem 1.3 the limit L is a measurable random metric on the probability space of h, chosen before the heat versions. In Theorem 1.8(i) one map D is chosen before every normalizer family, field law, sample and heat version, and the limit is D(h ω).
  - *Convergence in probability.* `LSCTendstoInProbability` is the subsequence form: for every sequence ε_n → 0 of positive numbers there is a subsequence along which, almost surely, the functions converge in the sense of the paper's Definition 1.2 (`LSCTendsto`). The supporting module [`SupercriticalLQGUniqueness.B2.LscTop.InProbability`](../../SupercriticalLQGUniqueness/B2/LscTop/InProbability.lean) characterizes this convergence notion of Theorem 1.3. It proves that the predicate is the subsequence form (`lscTendstoInProbability_iff_subseq`; for `LSCFun`-valued families, almost sure convergence in the topology of Definition 1.2 along a subsequence of every sequence, `lscTendstoInProbability_iff_subseq_tendsto`), that some metric induces the topology of Definition 1.2 (`exists_compatible_metric`), and that for every pseudo-emetric inducing that topology, every finite measure and a.e.-strongly measurable families, the predicate is Mathlib's `TendstoInMeasure` as ε → 0, that is, ordinary convergence in probability for that metric (`lscTendstoInProbability_iff_tendstoInMeasure`). It also proves that the limit is unique up to almost sure equality (`LSCTendstoInProbability.ae_eq_limit`). The module is not a frozen anchor; `Check.lean` audits its theorems with the six frozen ones.
  - *Split of Theorem 1.8.* The existence and uniqueness clauses are separate frozen theorems.
- **A4.** The files are ordinary (non-module) Lean files, because the pinned host and upstream libraries are non-modular. The frozen guard is run with `--allow-non-module`.
- **A20.** One internal endpoint-grid step of Theorem 1.13 uses a rotated finite grid. It suffices for the frozen uniqueness statement, and is not advertised as a proof of the paper's separately printed absolute-grid intermediate statement. Theorems 1.3 and 1.8 inherit it through Theorem 1.13.

## How Theorems 1.3 and 1.8(i) are proved

The proof follows the paper's proof of Theorems 1.3 and 1.8 (its Section 1.4).

1. **Subsequential limits.** Every sequence ε_n → 0 has a subsequence along which the re-scaled LFPP metrics converge to a weak LQG metric in Pfeffer's sense (Pfeffer's Theorem 1.7). The proof proves Pfeffer's Theorem 1.7 in the form Ding–Gwynne use, following Pfeffer's Section 2 with the corrections listed below, on the Skorokhod coupling of Ding–Gwynne's supercritical LFPP paper (its Section 5). That coupling is built from that paper's Sections 3 and 4, and from the positivity of the distance exponent. The tightness theorem of that paper (its Theorem 1.2) is not used as a separate statement: the subsequence extraction is part of the coupling.
2. **Weak LQG metric axioms.** Theorem 1.9 of Ding–Gwynne's up-to-constants comparison gives the comparability of the scaling constants 𝔠_r with r^{ξQ}. With it the limit satisfies Definition 1.12. This theorem is proved for LFPP subsequential limits, the only case the proof needs.
3. **Uniqueness of the limit.** By Theorem 1.13, two subsequential limits differ by a deterministic factor C. The median normalization gives C = 1, by a repaired argument (see below). So every sequence ε_n → 0 has a subsequence converging almost surely to the same limit, which is the frozen convergence statement.
4. **Theorem 1.8(i).** The limit map is a weak LQG metric, and the paper's weak-to-strong lemma (`lem-weak-to-strong`) makes it a strong LQG metric.
5. **Q > 0.** The supercritical LFPP paper cites the positivity theorem of Ding–Gwynne–Sepúlveda. Here Q > 0 is proved by their circuit induction on the discrete GFF, at one fixed level, transferred one-sidedly to the continuum LFPP. The explicit constants of their theorem are not proved; the proof only uses Q > 0.

Many intermediate results of the cited papers are proved in a variant, or bypassed by another route, that suffices for their use; the development repository's dependency graph records each one, node by node, as proved, inlined, bypassed or a variant. On the main proof path these variants are: Lemma 5.12 of the supercritical LFPP paper at aspect ratio 3/2; its large-annulus circuit estimate in a repaired form; its Theorem 1.2 in the Skorokhod form, with the scaling-constant clause proved separately; Theorem 1.9 of the up-to-constants comparison for LFPP subsequential limits only; the multiplicativity of the weak-to-strong scaling factor along the powers of one base b; only the scaling clause of the path-infimum scaling identity; and Pfeffer's `lem-prob` in a coupling form.

## Source corrections

The development audits found and repaired errors and gaps in intermediate statements and proof steps. None of them changes a frozen theorem. TeX labels refer to the pinned arXiv versions.

**Theorem 1.13 and the normalizer.** The finite-distance reading of length space; nonempty compact sets in set-distance and geodesic claims; the `r^{-ξQ}` normalization in set tightness; non-singular witnesses for the comparison events; separate relative and absolute dyadic radius grids; the direction of the large-around/small-across comparison; corrected reverse-Hölder exponents; and boundary-endpoint and planar-separation arguments.

**Ding–Gwynne, Theorems 1.3 and 1.8.**
- The median passage (C = 1) is not a limit of the ε-level medians: the closed-square crossing distance is not continuous for the topology of Definition 1.2, and there is a deterministic counterexample even for continuous length metrics. It is replaced by a lower bound, an upper bound through Weyl-penalized rational-circle distances, removability of the horizontal sides of the square at almost every height, and a surgery argument.
- In `lem-weak-to-strong`: Axiom V for a weak metric ("clear") is proved through a chain of annuli; that the rescaled metric satisfies the axioms ("easy to check") is proved axiom by axiom; and the scaling factor is shown to be 1 along the powers of one base by two-sided tightness, without the measurability in b and the Cauchy equation of the printed proof.

**Ding–Gwynne, supercritical LFPP (arXiv:2005.13576v2).**
- Crossing estimates between compact sets in an open set U are false for disconnected U (the internal distance is then infinite); they are read with U connected, which covers every use.
- The exact measurable geodesics asserted in the conditional-expectation lemma are replaced by measurably selected near-minimizers and an eventual-visit event, with Fatou's lemma.
- The Gaussian exponent of the hit term was misprinted; the corrected exponent is ξQ − ξ²/2 for ξ ≤ Q and Q²/2 for ξ > Q, still positive.
- The transfer of unit-rectangle tails to boxes of other fixed sizes, and the separator count, are replaced by same-index unit covers.
- In `lem-pt-dist`, two minimal annular crossings need not meet; they are joined through an around loop. Index, sign and set-operation slips in the same proof are corrected.
- The unbounded lower tail of `lem-perc-field` uses a finite cover by small boxes instead of one separator.
- The cited full-probability limit for the positivity of Q is false as stated; positivity is proved as described above. The circuit input of the induction is proved by a finite discrete Ray–Knight argument instead of loop soups, and the induction indices are repaired.

**Pfeffer (arXiv:2104.04020v3).**
- The localization hypothesis of `lem-general-metric-weyl` is vacuous as stated; near-minimal paths are localized by the unboundedness of limiting across costs.
- `prop-weyl-scaling` is false for a sequence of perturbations f_n → f (a counterexample with tall far bumps); a fixed perturbation is used, which is all its consumers need.
- The small-annuli input used for the fixed field is justified on the coupling, not for the fixed field; Weyl scaling is proved on the coupling and transported by laws.
- In `lem-as-circles`, pairs with a point are handled separately, since a loop around a point does not reach it.
- `lem-internal-radius` needs a length-space premise and a bounded domain, and Γ-convergence on a fixed metric ball can fail; it is replaced by a buffered Γ-convergence argument.
- Axiom V′ for the limit holds only through one-sided bounds, since across and around distances are not continuous for this topology.
- The patched metric for an unbounded continuous perturbation is built as one Borel map of the field, and the identification of internal metrics uses a barrier bump.
- The annulus iteration of `lem-iterate` is applied to finite-ε events, which are measurable functions of the field, and transferred to the limit.

**Ding–Gwynne, up-to-constants comparison (arXiv:2108.12060v1).** The ambient across cost is replaced by field-local internal crossings and around loops; heat-annulus tightness is derived from point crossings; bounds at compact scales and the paid-path estimates are proved without Jordan-curve assumptions; and the subadditivity lemma's positive slope is false (x_n = −n) and is replaced by a two-sided linear bound. The extension to all radii uses a rational-ratio clause that the LFPP subsequential limits satisfy (it is not part of Definition 1.12), so this step, like Theorem 1.9 itself, is proved only for those limits.

The development registers of these corrections are not part of this selected source snapshot.

## Reproduce the checks

The pinned toolchain is `leanprover/lean4:v4.34.0-rc2`; Mathlib is `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`. The included `lake-manifest.json` fixes the other dependencies. From the root of `leobon12/lean-formalizations`, with elan, Lake, Python 3 and the pinned dependencies available:

```sh
lake exe cache get
lake build SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPExponent \
  SupercriticalLQGUniqueness.Frozen.WeakLQGMetric_unique \
  SupercriticalLQGUniqueness.Frozen.ExistsUnique_isLFPPNormalizer \
  SupercriticalLQGUniqueness.Frozen.StrongLQGMetric_unique \
  SupercriticalLQGUniqueness.Frozen.Lfpp_tendstoInProbability \
  SupercriticalLQGUniqueness.Frozen.Exists_strongLQGMetric_lfppLimit \
  SupercriticalLQGUniqueness.B2.LscTop.InProbability
python3 -I results/supercritical-lqg-uniqueness/check_release.py
lake env lean results/supercritical-lqg-uniqueness/Check.lean
```

`Check.lean` runs `assert_no_sorry` and `#print axioms` on each of the six theorems and on the ten theorems of the characterization module. The expected axiom list for every one is `[propext, Classical.choice, Quot.sound]`. `check_release.py` checks the frozen files against the hashes, declarations and split policy of the frozen-anchor manifest. The public `scripts/verify.py --scan-only` checks the selected module closure, source hashes, import closure and forbidden proof tokens. `lake env leanchecker --fresh` can replay each frozen theorem module independently.

The import closure of the six theorems and the characterization module has 4,973 modules: 2,724 in this library and 2,249 already released modules of `LQGMetric` (metric geometry, GFF and LFPP tools), `QuantumZipper` (Gaussian and topological results), `LQGDimension` and `HigherDimLQGMetric`. These upstream results are proved in their libraries, not assumed as new axioms.

## About the source files

The 52 frozen definitions and six frozen theorems are copied byte for byte from the development revision recorded in `source-manifest.json`. Their docstrings are part of the frozen bytes: they cite lines of the pinned TeX source and the dates and decision records of the approval, and the two batch-2 theorem files still describe their proof body as the placeholder it was before the seal. The proof body itself is `by exact` the provider theorem.

Of the other 2,666 new files, 2,658 had development comments removed for this release (the remaining eight had none). Eleven internal names were given stable public names: one private namespace became `CoveredStep`, and ten theorems named after development work items were renamed. Their manifest rows record both the development hash and the exported hash, and every other Lean code token is unchanged. Module paths and internal declaration names otherwise keep their development names. These include `B2` for the second development batch, codes such as `P5`, `S2`, `J1` or `R68` for development work items, and version suffixes such as `_v2`; they carry no mathematical meaning. The public claims are exactly the six frozen theorems, with the characterization of their convergence notion described above.

The public frozen manifest is a metadata projection that replaces private approval-record paths and session identifiers with dates and request hashes; `manifest-provenance.json` records the SHA-256 of the authoritative development manifest.

## Mathematical provenance

The proof builds on [Ding–Gwynne, *Tightness of supercritical Liouville first passage percolation*](https://arxiv.org/abs/2005.13576), [Pfeffer, *Weak Liouville quantum gravity metrics with matter central charge c ∈ (−∞, 25)*](https://arxiv.org/abs/2104.04020), [Ding–Gwynne, *Up-to-constants comparison of Liouville first passage percolation and Liouville quantum gravity*](https://arxiv.org/abs/2108.12060), [Ding–Gwynne–Sepúlveda, *The distance exponent for Liouville first passage percolation is positive*](https://arxiv.org/abs/2005.13570) and [Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*](https://arxiv.org/abs/1905.00380). The upstream metric library formalizes work of [Gwynne–Miller on LQG metric existence and uniqueness](https://arxiv.org/abs/1905.00383) and [local metrics](https://arxiv.org/abs/1905.00379). The LFPP background also uses [Ding–Dubédat–Dunlap–Falconet on subcritical LFPP tightness](https://arxiv.org/abs/1904.08021), and estimates in the style of [Ding–Zeitouni–Zhang](https://arxiv.org/abs/1807.00422) (a heat-kernel variance bound) and [Ang](https://arxiv.org/abs/1904.09285) (discrete and continuum LFPP), proved here. Ding–Gwynne–Sepúlveda derive their circuit input from the isomorphism theorems of [Lupu](https://arxiv.org/abs/1402.0298) and [Aru–Lupu–Sepúlveda](https://arxiv.org/abs/1805.09204); this release proves it by a discrete Ray–Knight argument instead. For the topology of semicontinuous functions, the development cites G. Beer, "Upper semicontinuous functions and the Stone approximation theorem," *Journal of Approximation Theory* 34 (1982), 1–11; metric geometry arguments cite Burago–Burago–Ivanov, *A Course in Metric Geometry* (AMS, 2001). These are mathematical attributions, not axioms admitted by this Lean release.

## Credits and citation

The paper and its mathematical results belong to Ding and Gwynne. Cite the paper as: J. Ding and E. Gwynne, "Uniqueness of the critical and supercritical Liouville quantum gravity metrics," *Proceedings of the London Mathematical Society* (2023), arXiv:2110.00177v3. Cite the Lean source snapshot by repository URL and release commit. The development modules had no file-level author or copyright notices; the paper authors are credited here. The paper's text and PDF are not part of this source snapshot. The statements were frozen and audited following Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills) workflow.

[All released formalizations](../../README.md)
