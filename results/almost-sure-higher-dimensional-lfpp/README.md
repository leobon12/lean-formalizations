# Almost sure convergence of higher-dimensional LFPP

**Status.** Theorem 1.2 is `PROVED`, with its corollaries for nonnegative seeds and the non-vacuity of its hypotheses:
the eight frozen theorems of this formalization are sealed with two keys (the two frozen definitions are approved
whole-file anchors), and every one of them depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

This Lean 4 project formalizes the main result, Theorem 1.2, of *Almost sure convergence of higher-dimensional LFPP: an
upgrade from convergence in probability*, an **AI-generated, unrefereed manuscript** (17 pp.):
[PDF](https://leobon12.github.io/papers/lqg-2026-10-25/almost-sure-higher-dimensional-lfpp.pdf), SHA-256
`7476d6f42ab9d29855a5b61dfc3d91c008d3d37824cbb89eb2d3ddc06da93197`. Line numbers "l. N", in the Lean docstrings and
below, are lines of a plain-text extraction of that PDF (SHA-256
`c5bcc96de4e160e0a8dd9de097e639c33f7ac25e9e5bb5ac941f12c48fba7636`), which is not included here.

In words: fix d ≥ 3, ξ > 0, a real radial seed κ ∈ C_c^∞(ℝ^d) with ∫κ² = 1 (no sign condition) and the kernel K of the
paper's (1.2). Let h be the whole-space log-correlated Gaussian field normalized by h₁(0) = 0, h*_ε = h ∗ K_ε, D^ε_h the
LFPP distance (1.3) and 𝔞_ε the median (1.4) of D^ε_h(0, e₁). If a metric assignment D satisfies the paper's
Assumption 1.1, then almost surely, for every compact F ⊂ ℝ^d, sup_{x,y∈F} |𝔞_ε⁻¹ D^ε_h(x, y) − D_h(x, y)| → 0 as ε ↓ 0
through all positive reals. For nonnegative seeds Assumption 1.1 is proved, so the convergence holds with no assumption.

| Paper item | Lean declaration (frozen) | Status |
| --- | --- | --- |
| Theorem 1.2, every admissible seed, under Assumption 1.1 | `HigherDimLFPPAS.asConvergence` | **PROVED** (two keys) |
| Theorem 1.2 for nonnegative seeds, no assumption: a median-one strong metric is the limit | `HigherDimLFPPAS.asConvergence_nonneg` | **PROVED** (two keys) |
| Theorem 1.2 for nonnegative seeds, no assumption: every median-one strong metric is the limit | `HigherDimLFPPAS.asConvergence_medianOne` | **PROVED** (two keys) |
| Assumption 1.1 holds for nonnegative seeds (one assignment for all of them, when √(2d) < Q(ξ)) | `HigherDimLFPPAS.assumption11_nonvacuous` | **PROVED** (two keys) |
| The hypotheses of Theorem 1.2 are jointly satisfiable | `HigherDimLFPPAS.asConvergence_nonvacuous` | **PROVED** (two keys) |
| §1: K is real, smooth, with integral one, for every admissible seed | `HigherDimLFPPAS.convKernel_seed` | **PROVED** (two keys) |
| §1: h ∗ K_ε exists for each ε | `HigherDimLFPPAS.convMollify_spec_seed` | **PROVED** (two keys) |
| Appendix A: h ∗ K_ε converges and is jointly continuous in (ε, z) on one event | `HigherDimLFPPAS.convMollify_joint_seed` | **PROVED** (two keys) |
| §1: the seeds | `HigherDimLFPPAS.IsAdmissibleSeed` | frozen definition |
| Assumption 1.1 | `HigherDimLFPPAS.Assumption11` | frozen definition |

## Exact frozen statements

The declarations below are copied from the frozen files `HigherDimLFPPAS/Frozen/`, which ship byte for byte as sealed.
The proof body of each theorem is `by exact` its provider in `HigherDimLFPPAS.Implementation` (the provider states the
same type). The files open `MeasureTheory`, `Filter`, `Topology`, `HigherDimLQGMetric` (and `HigherDimLQGContinuity` for the
corollaries), and `HigherDimLFPP (Rd)`.

```lean
structure IsAdmissibleSeed {d : ℕ} (κ : Rd d → ℝ) : Prop where
  contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) κ
  hasCompactSupport : HasCompactSupport κ
  radial : ∀ z w : Rd d, ‖z‖ = ‖w‖ → κ z = κ w
  integral_sq : ∫ z, κ z ^ 2 = 1
```

```lean
structure Assumption11 (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ) (D : DistRd d → ContMetric d)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistRd d) : Prop where
  /-- `Q = Q(ξ) > √(2d)` (l. 103) -/
  subcritical : Real.sqrt (2 * d) < distExp d ξ
  /-- the measurable assignment and (i)–(iv) (l. 90–106) -/
  strong : IsStrongExpMetric d ξ (distExp d ξ) D
  /-- (v), (1.6): `𝔞_ε⁻¹ D^ε_h → D_h` in probability, locally uniformly (l. 108–111) -/
  conv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
    (fun ω => (D (h ω)).1)
```

**Theorem 1.2.**

```lean
theorem asConvergence :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ →
    ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
    ∀ D : DistRd d → ContMetric d,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
      IsNormalizedLGF h P → Assumption11 d ξ κ D P h →
      ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
        Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
          (𝓝[>] 0) (𝓝 0) :=
```

**Nonnegative seeds, with no assumption.** `HigherDimLFPP.IsLFPPKernel κ` is `IsAdmissibleSeed κ` plus κ ≥ 0, and
`IsMedianOne d D` says that 1 is a median of D_h(0, e₁) under the law of the normalized field.

```lean
theorem asConvergence_nonneg :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∃ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D ∧ IsMedianOne d D ∧
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
              edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) :=
```

```lean
theorem asConvergence_medianOne :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D → IsMedianOne d D →
      ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P →
        ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
          Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
              edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
            (𝓝[>] 0) (𝓝 0) :=
```

**Non-vacuity.**

```lean
theorem assumption11_nonvacuous :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∃ D : DistRd d → ContMetric d, ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      IsAdmissibleSeed κ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → Assumption11 d ξ κ D P h :=
```

```lean
theorem asConvergence_nonvacuous :
    ∀ d : ℕ, 3 ≤ d → ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ ∈ Set.Ioo (0 : ℝ) ξ₀,
      ∃ (κ : Rd d → ℝ) (D : DistRd d → ContMetric d) (Ω : Type) (_ : MeasurableSpace Ω)
        (P : Measure Ω) (h : Ω → DistRd d),
        IsAdmissibleSeed κ ∧ IsProbabilityMeasure P ∧ IsNormalizedLGF h P ∧ Assumption11 d ξ κ D P h :=
```

**The kernel and the convolution field, for every admissible seed.** These pin the meaning of the definitions
`convKernel` (the real part of 𝓕⁻¹ K̂), `convTrunc` and `convMollify` (h ∗ K_ε as a limit of truncated pairings) of
`HigherDimLQGMetric` on signed seeds: the real part loses nothing, no junk branch is taken, and h ∗ K_ε is defined for
all ε > 0 and z on one event.

```lean
theorem convKernel_seed :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      (∀ x : Rd d, (𝓕⁻ (fun ζ : Rd d => (kernelSymbol κ ζ : ℂ)) x).im = 0) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ ∫ x, convKernel κ x = 1 :=
```

```lean
theorem convMollify_spec_seed :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) :=
```

```lean
theorem convMollify_joint_seed :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P,
          (∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
            Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z))) ∧
          ContinuousOn (fun p : ℝ × Rd d => convMollify κ p.1 (h ω) p.2) (Ioi 0 ×ˢ univ) :=
```

The objects come from the released `HigherDimLQGMetric` library (the higher-dimensional exponential metrics release):
`IsNormalizedLGF h P` is the whole-space log-correlated Gaussian field with covariance log(1/|x − y|) on mean-zero test
functions, normalized by h₁(0) = 0; `lfppDist κ ξ ε h` is the LFPP distance (1.3) of h*_ε = `convMollify κ ε h` over
piecewise C¹ paths; `aEps κ ξ ε` is the lower median (1.4) of `lfppDist κ ξ ε h (0, e₁)` under the law of the normalized
field; `ContMetric d` is the type of continuous metrics on ℝ^d inducing the Euclidean topology; `IsStrongExpMetric` is the
four strong axioms of the higher-dimensional exponential metric (length metric, locality, Weyl scaling, coordinate change);
`distExp d ξ` is the LFPP distance exponent Q(ξ); `TendstoInProbLU` is convergence in probability, uniformly on compact
subsets of ℝ^d × ℝ^d.

## Statement scope and disclosures

These points are part of the approved statements and matter when comparing them with the paper. An independent
statement audit checked every binder against the paper before the statements were frozen: no hypothesis beyond the
paper's, and an independent transcription of Theorem 1.2 was proved equivalent in Lean to `asConvergence`.

1. **Conditional main theorem, signed seeds.** `asConvergence` keeps the paper's hypothesis: Assumption 1.1 for the given
   assignment D. It covers every admissible seed, sign-changing ones included, as the paper does (l. 70–71: "It need not
   be nonnegative").
2. **Unconditional results only for nonnegative seeds.** `asConvergence_nonneg`, `asConvergence_medianOne` and
   `assumption11_nonvacuous` are for seeds κ ≥ 0 and in the paper's regime √(2d) < Q(ξ); there Assumption 1.1 is supplied
   by the released theorem `HigherDimLQGMetric.theorem12`. Whether Assumption 1.1 holds for a sign-changing seed is not
   claimed. `asConvergence_nonvacuous` shows that the hypotheses of `asConvergence` are jointly satisfiable for every
   d ≥ 3 and all small ξ > 0.
3. **The reading of Assumption 1.1 (i)–(iv).** The paper says that these are "exactly the conclusions needed from the
   earlier characterization" (l. 115–116); they are read as the strong axioms `IsStrongExpMetric d ξ (distExp d ξ) D` of
   the higher-dimensional exponential metrics paper, with three conventions of the released definition:
   - every value of the assignment is a continuous metric inducing the Euclidean topology (`ContMetric d`), for every
     distribution and not only almost surely; an assignment of the paper's kind can be changed on a set that is null for
     every field of the class so that this holds, and the changed assignment still satisfies the axioms;
   - the axioms are asked for every log-correlated field plus a possibly dependent random continuous function, the field
     class of that paper (the paper here says "plus a continuous function");
   - (iv) is stated as D_h(ru + z, rv + z) = D_{h(r·+z) + Q log r}(u, v) for every field of the class. The statement audit
     shows by Weyl scaling that this is equivalent to (1.5) together with the paper's "covariance identities after
     continuous perturbations" (l. 103–106); that equivalence is a paper-level argument, not a Lean theorem of this
     release.
4. **Assumption 1.1 (v)** is convergence in probability (1.6) for the given field on its own probability space, as the
   paper says ("on the original field probability space", l. 108). The alternative that quantifies (v) over every
   normalized field adds a premise the paper does not state; it was rejected.
5. **The exponent.** Q is `distExp d ξ`, the LFPP distance exponent Q(ξ). A strong assignment at (ξ, Q) forces Q = Q(ξ),
   so nothing is lost for signed seeds.
6. **Outer measures.** Probabilities of sets that may be non-measurable are outer measures. As a hypothesis (in
   `TendstoInProbLU`) this is the stronger reading; the conclusion `∀ᵐ` is the complete-measure reading. The proof
   establishes the a.e.-measurability it needs.
7. **The pathwise convolution.** `lfppDist` uses the canonical h ∗ K_ε of each realized field (a limit of truncated
   pairings), not a chosen version. The paper chooses a jointly differentiable version (Appendix A); `convMollify_joint_seed`
   proves that the canonical object agrees with it: almost surely the truncations converge for all ε > 0 and z at once,
   and (ε, z) ↦ h*_ε(z) is continuous. This is proved, not assumed. The kernel statements hold for d ≥ 2, a wider range
   than the paper's d ≥ 3.
8. **The conclusion** is the paper's (1.7): the supremum is taken in [0, ∞] (`edist` of real numbers, complete-lattice
   `⨆`), one probability-one event serves every compact set, and ε ↓ 0 through all positive reals (`𝓝[>] 0`).
9. **Instance-path versions.** Four frozen files gained one import after approval (`import Mathlib` for the three
   convergence theorems, `import Mathlib.Analysis.CStarAlgebra.Classes` for `convKernel_seed`), because the providers'
   imports changed the instance path chosen inside the statements (`SupSet ℝ≥0∞`, `NormedSpace ℂ ℂ`). The statement text is
   unchanged, and the old and new elaborations were proved equal by `rfl`.

## What is not claimed

- Assumption 1.1 for sign-changing seeds: the unconditional results are for κ ≥ 0 only.
- The equivalence of the (iv) convention with the printed (1.5) as a Lean theorem (item 3).
- The paper's intermediate lemmas as public results: they are formalized inside the library on the way to Theorem 1.2,
  some in corrected form, but only the frozen statements above are claimed.
- The manuscript is AI-generated and unrefereed; the release proves the Lean statements above, not every claim of the
  manuscript.

## Cited inputs

No literature result is assumed. The convergence in probability (1.6) and the strong axioms are the paper's own
hypothesis (Assumption 1.1); every other input is proved here or in an already released library:

| Input of the paper | Treatment |
| --- | --- |
| The characterization of the higher-dimensional exponential metric [5] | the released `HigherDimLQGMetric` library; its `theorem12` gives Assumption 1.1 for nonnegative seeds |
| Contreras Hip–Zhuang, the shell independence input (their Lemma 2.7) | the released shell-decoupling theorem `HigherDimLQGMetric.lemmaA1`, in the centred shell form the paper uses |
| Contreras Hip–Zhuang, the LFPP comparison estimates of their Section 4 | for signed seeds, rederived from Assumption 1.1 (v) and the localization bound (3.9), without the nonnegativity that the literature uses for tightness |
| Ding–Gwynne–Zhuang tightness | used only through `theorem12`, for nonnegative seeds; not used for signed seeds |
| Bingham–Goldie–Teugels, regular variation | not used: the scaling of the median 𝔞_ε is derived by an elementary argument |
| Borell's inequality | not used directly; its use inside the shell-independence input is covered by the released proof of that input |
| The identification of median-one strong metrics | the released `HigherDimLQGContinuity.theorem11Xi` (for `asConvergence_medianOne`) |

## How it was checked

The project follows Scott Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills)
workflow.

1. **Planning.** Refute-first audits of every section and cited input, and a corrected rewrite of the proofs.
2. **Statement.** The ten statements were frozen one declaration per file, pinned by a hash manifest (the bytes around the
   proof body and the elaborated types), after the independent statement audit described above.
3. **Proof.** Each frozen theorem has a provider theorem with exactly its type; the frozen body is `by exact` the provider.
4. **Two-key seal.** A theorem is `PROVED` only after both keys. Key 1: the frozen-anchor checker, the build, unchanged
   elaborated types and statement-closure fingerprint, and `#print axioms` with standard axioms only. Key 2: an independent
   seal audit by an auditor who did not write the statement or its proof: fidelity to the paper, no proof step smuggled in
   as a hypothesis, the provider chain, axioms and a kernel replay. Three such audits covered the eight theorems, each with
   `VERDICT: PASS`; the last one replayed the whole closure of Theorem 1.2 in a fresh kernel
   (`leanchecker --fresh HigherDimLFPPAS.Frozen.AsConvergence`, exit 0) and the remaining modules of the two corollaries.
5. **Release checks.** On the release tree (the development commit staged onto the public `main`): every new module (the
   111 files of this library and the new upstream module below) was compiled from empty project artifacts against 3,332
   released modules whose compiled files are trace-linked to the public source bytes, with no error and no `sorry`;
   `Check.lean` reports only `propext`, `Classical.choice` and `Quot.sound` for each of the eight theorems; the public source
   scan passes.

## What is in the library

The library `HigherDimLFPPAS` ships 111 Lean files: the import closure of the ten frozen files. The development root
module and one module outside that closure are not shipped. *Lines* are physical lines; *code lines* are neither blank nor
entirely inside comments.

| Part | Directories | Modules | Lines | Code lines |
| --- | --- | ---: | ---: | ---: |
| Gaussian field estimates and Appendix A | `Field`, `Gauss`, `Windows` | 22 | 4,707 | 3,922 |
| Metric preliminaries, localization, properness, scaling and rescaling | `Bridge`, `Det`, `Localize`, `Proper`, `Scaling`, `Rescale` | 23 | 3,858 | 3,187 |
| Shell comparison, Lemma 2.7 and the annulus events of Section 3 | `Annulus`, `Coarse`, `Covering`, `Shell` | 14 | 4,400 | 3,852 |
| Improvement and iteration (Propositions 4.1 and 5.1) | `Improve`, `Iterate`, `Sharp` | 10 | 3,459 | 2,951 |
| The median normalizer (Lemma 2.5) | `Glue`, `Normalizer` | 9 | 1,657 | 1,248 |
| Endpoint estimates and the assembly of Theorem 1.2 (Sections 6–7) | `Endpoint`, `Main` | 8 | 2,667 | 2,247 |
| Kernel and field facts for signed seeds | `Signed` | 6 | 4,406 | 3,695 |
| Shared proof interfaces | `Core` | 1 | 587 | 335 |
| **Proof modules** | | **93** | **25,741** | **21,437** |
| Frozen statements (2 definitions, 8 theorems) | `Frozen` | 10 | 544 | 220 |
| Providers of the eight frozen theorems | `Implementation` | 8 | 373 | 208 |
| **Total shipped** | | **111** | **26,658** | **21,865** |

The release also adds one module of the released `HigherDimLQGMetric` library that its earlier release did not need,
`HigherDimLQGMetric.Sec4.AEpsLocBdd`. The import closure of the shipped files has 3,444 modules: these 112 and 3,332
modules of already released libraries, unchanged: `HigherDimLQGMetric` (1,301), `QuantumZipper` (734), `LQGMetric` (667),
`HigherDimLQGContinuity` (446), `HigherDimLFPP` (97), `GaussianLQG` (49) and `LQGDimension` (38). Their results are proved
in their libraries, not assumed.

## About the source files

All files are copied byte for byte from the development commit recorded in `source-manifest.json`, with one exception:
in `HigherDimLFPPAS/Core/Interfaces.lean` a comment that named a private working folder was shortened; the file's manifest
row records both hashes, and its code is unchanged. The ten frozen files are unchanged. Comments and docstrings otherwise
keep their development wording: some cite the development's rulings (L1–L12), audits, work items and planning files,
which are not part of this release. Named propositions in `HigherDimLFPPAS.Core` (`Setting`, `PairLaw`, `Lemma24Conv`,
...) are internal interfaces between proof steps: `Setting` is built from the frozen hypotheses, every interface that the
proof consumes is the conclusion of a proved theorem, and none occurs in a frozen statement.

## Reproduce the checks

The toolchain is `leanprover/lean4:v4.34.0-rc2` and Mathlib is `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`; the included
`lake-manifest.json` pins the other dependencies. From the root of `leobon12/lean-formalizations`, with elan, Lake and
Python 3:

```sh
lake exe cache get
lake build HigherDimLFPPAS.Frozen.AsConvergence HigherDimLFPPAS.Frozen.AsConvergenceNonneg \
  HigherDimLFPPAS.Frozen.AsConvergenceMedianOne HigherDimLFPPAS.Frozen.Assumption11Nonvacuous \
  HigherDimLFPPAS.Frozen.AsConvergenceNonvacuous HigherDimLFPPAS.Frozen.ConvKernelSeed \
  HigherDimLFPPAS.Frozen.ConvMollifySpecSeed HigherDimLFPPAS.Frozen.ConvMollifyJointSeed
lake env lean results/almost-sure-higher-dimensional-lfpp/Check.lean
python3 -I scripts/verify.py --scan-only
```

`Check.lean` runs `assert_no_sorry` and `#print axioms` on each of the eight theorems; every reported axiom must be one
of `propext`, `Classical.choice` and `Quot.sound`. `scripts/verify.py --scan-only` checks the selected module closure,
the source hashes, the import closure and forbidden proof tokens. `lake env leanchecker --fresh
HigherDimLFPPAS.Frozen.AsConvergence` replays the whole closure of Theorem 1.2 in a fresh kernel (about 20 minutes and
10 GB of memory).

## Credits

The manuscript is the author's own AI-generated paper, linked above at its website address with its SHA-256. Cite the
Lean source snapshot by repository URL and release commit. The statements were frozen and audited following Scott
Armstrong's LeanAutoformalizationSkills workflow.

[All released formalizations](../../README.md)
