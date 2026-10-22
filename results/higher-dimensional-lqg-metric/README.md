# Higher-dimensional exponential metrics: axiomatic existence and uniqueness

Lean formalization of **Theorems 1.2 and 1.4** of *Higher-dimensional exponential metrics: a proposed
axiomatic existence and uniqueness proof* (2 October 2026; [AI research
paper](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/higher-dimensional-lqg-metric.pdf),
AI-generated and unrefereed), developed under Leonardo Bonanno's direction with AI assistance. The paper
presents its argument as a proposed proof that had not been independently verified. Every step of it, and
of the results it imports, was audited before the statements were frozen; the corrections are listed
below.

The formalization covers **both theorems, in every dimension d ≥ 3, with no assumptions**. For the
whole-space log-correlated Gaussian field and every ξ > 0 with Q(ξ) > √(2d), there is a metric assignment
satisfying the four strong axioms of the paper; any two such assignments agree up to a deterministic
positive constant; normalized Liouville first passage percolation (LFPP) converges to it; and any two
assignments of the auxiliary weak class are deterministic positive multiples of one another. The only
hypotheses are the definitions of the objects. The paper imports its existence input from Contreras
Hip–Zhuang [1] (subsequential LFPP limits are weak metrics, sharp normalizers, a comparison criterion,
shell independence, diameter moments), whose construction rests on the tightness theorem of
Ding–Gwynne–Zhuang [2]. **Both are proved here**, together with the kernel independence of the distance
exponent Q(ξ) (in place of [6]), a codimension-two nonseparation theorem (in place of Krupski–Valov [5])
and the Gaussian Hölder inequality of Chen–Dafnis–Paouris [7].

[Theorem 1.2](../../HigherDimLQGMetric/Frozen/Theorem12.lean#L42-L55) · [Theorem
1.4](../../HigherDimLQGMetric/Frozen/Theorem14.lean#L35-L42) · [Frozen
definitions](../../HigherDimLQGMetric/Frozen/) · [Proofs](../../HigherDimLQGMetric/Assembly/) · [Final
assembly](../../HigherDimLQGMetric/Main/) · [Focused certificate](Check.lean) · [Verification
record](verification.json)

## The theorems

Fix d ≥ 3 and ξ > 0. The distance exponent Q(ξ) is defined through the white-noise approximations of LFPP
in dimension d: their distances D_ε from 0 to e₁, through paths in (−2, 2)^d, satisfy log D_ε / log ε → 1
− ξQ(ξ) in probability. It exists and does not depend on the kernel (`distExp_spec`). Throughout, Q(ξ) >
√(2d), the subcritical range, which contains an interval (0, ξ₀) (`subcritical_nonempty`).

The field h is a whole-space log-correlated Gaussian field (LGF) on ℝ^d: a random distribution whose
pairings with mean-zero test functions are centred Gaussian, with covariance ∬ φ(x) log(1/‖x − y‖) ψ(y)
dx dy. Its sphere averages are written h_r(z), and h_1(0) = 0 fixes the additive constant when one is
needed. A metric assignment is a measurable map h ↦ D_h from distributions to continuous metrics on ℝ^d
that induce the Euclidean topology.

**Definition 1.1** (the four strong axioms at (ξ, Q)). Whenever the input is an LGF plus a possibly
random continuous function:

- **(I)** D_h is a length metric;
- **(II)** for deterministic open U, the internal metric D_h(·, ·; U) is a measurable function of h
  restricted to U;
- **(III)** almost surely, simultaneously for all continuous f, D_{h+f} = e^{ξf}·D_h, the metric that
  minimizes the integral of e^{ξf} against D_h-arclength;
- **(IV)** for fixed r > 0 and z ∈ ℝ^d, almost surely, simultaneously for all u, v, D_h(ru + z, rv + z) =
  D_{h(r·+z)+Q log r}(u, v).

**Theorem 1.2.** There is an assignment satisfying the four strong axioms. Any two such assignments at
the same (d, ξ, Q) differ almost surely by a deterministic positive constant, simultaneously on all
endpoint pairs and after all continuous perturbations of the field. For the convolution approximations of
[1, Remark 1.1], the LFPP metrics D^ε_h normalized by the median 𝔞_ε of D^ε_h(0, e₁) for h_1(0) = 0
converge in probability, locally uniformly, to the assignment; so do those of an LGF plus a bounded
continuous function.

**Definition 1.3 and Theorem 1.4.** The weak class keeps (I)–(III), requires translation covariance, and
requires deterministic normalizers c_r for which c_r⁻¹ e^{−ξ h_r(0)} D_h(r·, r·) is tight, locally
uniformly, over 0 < r < R for every R (over all r > 0 when the continuous function is bounded), with
every limit inducing the Euclidean topology. Any two assignments in this weak class with the same ξ are
deterministic positive multiples of one another.

The proof declarations are `HigherDimLQGMetric.theorem12` and `HigherDimLQGMetric.theorem14`. Their
statements, copied from
[`HigherDimLQGMetric/Frozen/Theorem12.lean`](../../HigherDimLQGMetric/Frozen/Theorem12.lean#L42-L55) and
[`HigherDimLQGMetric/Frozen/Theorem14.lean`](../../HigherDimLQGMetric/Frozen/Theorem14.lean#L35-L42)
(inside `namespace HigherDimLQGMetric`, with `open MeasureTheory Filter Topology` and `open HigherDimLFPP
(Rd)`), are:

```lean
theorem theorem12 :
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

theorem theorem14 :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
    ∀ (D D' : DistRd d → ContMetric d) (c c' : ℝ → ℝ),
      IsWeakExpMetric d ξ D c → IsWeakExpMetric d ξ D' c' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=
```

Their proofs are `by exact HigherDimLQGMetric.theorem12_impl` and `by exact
HigherDimLQGMetric.theorem14_impl`
([`Assembly/Theorem12.lean`](../../HigherDimLQGMetric/Assembly/Theorem12.lean),
[`Assembly/Theorem14.lean`](../../HigherDimLQGMetric/Assembly/Theorem14.lean)). The statements hold for
every assignment, every probability space and every input in the classes the paper names. They were
frozen and audited independently against the paper before the proofs were written. Sealing changed only
the one-line proof bodies; a hash of the elaborated statements confirms that they are unchanged.

### The other frozen theorems

Nine further theorems were frozen with the main ones. Two are the uniqueness statements that the paper's
new argument (§§2–10) proves without LFPP; one shows that the weak class is inhabited. Six certify that
the definitions used by the statements mean what the paper means: the exponent exists and the subcritical
range is nonempty, the normalized field exists and has a unique law, the kernel is genuine, and the
limits that define sphere averages and the convolution exist. Their statements, from
[`HigherDimLQGMetric/Frozen/`](../../HigherDimLQGMetric/Frozen/), are:

```lean
-- Theorem 1.4 in the weak class with the sharp normalizers c_r = r^{ξQ}, for every Q > √(2d)
theorem theorem14Sharp :
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsSharpWeakExpMetric d ξ Q D → IsSharpWeakExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=

-- the uniqueness clause of Theorem 1.2, for every Q > √(2d)
theorem strongUniqueness :
    ∀ (d : ℕ) (ξ Q : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < Q →
    ∀ D D' : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ Q D → IsStrongExpMetric d ξ Q D' →
      ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusCont h P →
          ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
            (D' (addFun (h ω) f)).1 (u, v) = C * (D (addFun (h ω) f)).1 (u, v) :=

-- non-vacuity: the weak class with sharp normalizers at Q(ξ) is inhabited
theorem sharpWeak_nonempty :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ → Real.sqrt (2 * d) < distExp d ξ →
      ∃ D : DistRd d → ContMetric d, IsSharpWeakExpMetric d ξ (distExp d ξ) D :=

-- Q(ξ) exists, does not depend on the kernel, and is unique
theorem distExp_spec :
    ∀ (d : ℕ), 2 ≤ d → ∀ ξ : ℝ, 0 < ξ → ∀ Q : ℝ, IsDistanceExponent d ξ Q ↔ Q = distExp d ξ :=

-- the subcritical range contains an interval (0, ξ₀)
theorem subcritical_nonempty :
    ∀ (d : ℕ), 2 ≤ d → ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, Real.sqrt (2 * d) < distExp d ξ :=

-- the LGF normalized by h_1(0) = 0 exists and its law is unique
theorem normLGFLaw_spec :
    ∀ (d : ℕ), 2 ≤ d → IsProbabilityMeasure (normLGFLaw d) ∧ IsNormalizedLGF id (normLGFLaw d) ∧
      ∀ μ : Measure (DistRd d), IsProbabilityMeasure μ → IsNormalizedLGF id μ → μ = normLGFLaw d :=

-- the kernel K of [1, Remark 1.1] is smooth with unit mass
theorem convKernel_smooth_integral :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ) ∧ ∫ x, convKernel κ x = 1 :=

-- the limit that defines the sphere average h_r(z) exists almost surely
theorem sphereAvg_spec :
    ∀ (d : ℕ), 2 ≤ d → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P → ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫ u, h ω (bumpTest n (z + r • u)) ∂(unitSphereProb d))
          atTop (𝓝 (sphereAvg (h ω) r z)) :=

-- the limit that defines h * K_ε exists almost surely, at every point
theorem convMollify_spec :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsLGFPlusBddCont h P → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ z : Rd d,
          Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z)) :=
```

Line-anchored sources: [`theorem14Sharp`](../../HigherDimLQGMetric/Frozen/Theorem14Sharp.lean#L35-L42),
[`strongUniqueness`](../../HigherDimLQGMetric/Frozen/StrongUniqueness.lean#L34-L41),
[`sharpWeak_nonempty`](../../HigherDimLQGMetric/Frozen/SharpWeakNonempty.lean#L33-L35),
[`distExp_spec`](../../HigherDimLQGMetric/Frozen/DistExpSpec.lean#L31-L32),
[`subcritical_nonempty`](../../HigherDimLQGMetric/Frozen/SubcriticalNonempty.lean#L32-L33) (with `open
Set`), [`normLGFLaw_spec`](../../HigherDimLQGMetric/Frozen/NormLGFLawSpec.lean#L33-L35),
[`convKernel_smooth_integral`](../../HigherDimLQGMetric/Frozen/ConvKernelSmoothIntegral.lean#L34-L36),
[`sphereAvg_spec`](../../HigherDimLQGMetric/Frozen/SphereAvgSpec.lean#L34-L38) and
[`convMollify_spec`](../../HigherDimLQGMetric/Frozen/ConvMollifySpec.lean#L35-L39). The sanity anchors
are stated for d ≥ 2, a wider range than the theorems need.

[`Check.lean`](Check.lean) restates all eleven statements verbatim and checks that the frozen
declarations prove them. It then derives, in dimension three, a subcritical parameter ξ, a strong
assignment at Q(ξ), the normalized field and an admissible kernel to which the LFPP clause of Theorem 1.2
applies, and an inhabitant of the weak class of Theorem 1.4. So the hypotheses of both theorems can be
met.

## The frozen definitions

Each of the 46 project definitions in the statements is frozen in its own file under
[`HigherDimLQGMetric/Frozen/`](../../HigherDimLQGMetric/Frozen/). The other names come from Mathlib, from
the [higher-dimensional LFPP release](../higher-dim-lfpp/) and from the [LQG metric
release](../lqg-metric/). The main ones:

| Paper | Lean | Definition |
| --- | --- | --- |
| ℝ^d, test functions, distributions | [`Rd d`](../../HigherDimLFPP/Frozen/Rd.lean#L20), [`TestRd d`](../../HigherDimLQGMetric/Frozen/TestRd.lean#L23), [`DistRd d`](../../HigherDimLQGMetric/Frozen/DistRd.lean#L24) | `EuclideanSpace ℝ (Fin d)`; Mathlib's smooth compactly supported test functions and its distributions. Distributions carry the σ-algebra generated by the pairings ([`DistOn.measurableSpace`](../../HigherDimLQGMetric/Frozen/DistOnMeasurableSpace.lean#L29)). |
| h restricted to U, h + f, h + c, h(r· + z) | [`restrictTo`](../../HigherDimLQGMetric/Frozen/RestrictTo.lean#L25), [`addFun`](../../HigherDimLQGMetric/Frozen/AddFun.lean#L23), [`addConst`](../../HigherDimLQGMetric/Frozen/AddConst.lean#L23), [`affineComp`](../../HigherDimLQGMetric/Frozen/AffineComp.lean#L26) | Restriction to test functions supported in U; addition of the distribution ∫ f φ of a continuous f ([`ofCont`](../../HigherDimLQGMetric/Frozen/OfCont.lean#L28)); ⟨h(r· + z), φ⟩ = r^{−d} ⟨h, φ((· − z)/r)⟩. |
| h_r(z) | [`sphereAvg h r z`](../../HigherDimLQGMetric/Frozen/SphereAvg.lean#L30) | The limit, as n → ∞, of the average over the sphere of radius r about z of the pairings of h with radial unit-mass bumps of scale 2^{−n} ([`bumpTest`](../../HigherDimLQGMetric/Frozen/BumpTest.lean#L29), [`unitSphereProb`](../../HigherDimLQGMetric/Frozen/UnitSphereProb.lean#L28)). The limit exists almost surely (`sphereAvg_spec`). |
| the LGF | [`IsWholeSpaceLGF h P`](../../HigherDimLQGMetric/Frozen/IsWholeSpaceLGF.lean#L34) | h is measurable, and its pairings with mean-zero test functions form a centred Gaussian process with covariance ∬ φ(x)(−log‖x − y‖)ψ(y) dx dy ([`logCovRd`](../../HigherDimLQGMetric/Frozen/LogCovRd.lean#L28)). The additive constant is arbitrary and may be random. |
| h_1(0) = 0 | [`IsNormalizedLGF h P`](../../HigherDimLQGMetric/Frozen/IsNormalizedLGF.lean#L26), [`normLGFLaw d`](../../HigherDimLQGMetric/Frozen/NormLGFLaw.lean#L29) | An LGF with sphereAvg h 1 0 = 0 almost surely, and its law, which exists and is unique (`normLGFLaw_spec`). |
| the inputs | [`IsLGFPlusCont h P`](../../HigherDimLQGMetric/Frozen/IsLGFPlusCont.lean#L29), [`IsLGFPlusBddCont h P`](../../HigherDimLQGMetric/Frozen/IsLGFPlusBddCont.lean#L28) | h minus some measurable random continuous (resp. bounded continuous) function f, on the same probability space, is an LGF; f may depend on the field. |
| metrics | [`ContMetric d`](../../HigherDimLQGMetric/Frozen/ContMetric.lean#L26), [`.internal`](../../HigherDimLQGMetric/Frozen/ContMetricInternal.lean#L29), [`.IsLength`](../../HigherDimLQGMetric/Frozen/ContMetricIsLength.lean#L25) | Continuous metrics on ℝ^d inducing the Euclidean topology ([`IsContinuousMetric`](../../HigherDimLQGMetric/Frozen/IsContinuousMetric.lean#L27)), as a subspace of C(ℝ^d × ℝ^d, ℝ) with the local uniform topology; the internal metric D(z, w; U) in [0, ∞] and the length-space property, from the LQG metric release ([`internalEDist`](../../LQGMetric/Metric/LengthSpace.lean#L118), [`IsLengthSpace`](../../LQGMetric/Metric/LengthSpace.lean#L98)). |
| e^{ξf}·D | [`weylScale ξ f D z w`](../../HigherDimLQGMetric/Frozen/WeylScale.lean#L33) | The infimum, over paths from z to w parametrized by D-length, of ∫ e^{ξ f(P(t))} dt, in [0, ∞]. |
| Definition 1.1 | [`IsStrongExpMetric d ξ Q D`](../../HigherDimLQGMetric/Frozen/IsStrongExpMetric.lean#L41) | Measurability and Axioms (I)–(IV), each required for every input `IsLGFPlusCont h P` on every probability space. |
| Definition 1.3 | [`IsWeakExpMetric d ξ D c`](../../HigherDimLQGMetric/Frozen/IsWeakExpMetric.lean#L44) | Measurability, (I)–(III), translation covariance, positive normalizers c, and tightness of [`normalizedAtScale`](../../HigherDimLQGMetric/Frozen/NormalizedAtScale.lean#L26) over 0 < r < R for every R (over r > 0 for bounded perturbations), in the sense of [`TightOver`](../../HigherDimLQGMetric/Frozen/TightOver.lean#L33): the laws are tight and every law in their weak closure is carried by continuous metrics inducing the Euclidean topology. |
| weak class with c_r = r^{ξQ} | [`IsSharpWeakExpMetric d ξ Q D`](../../HigherDimLQGMetric/Frozen/IsSharpWeakExpMetric.lean#L26) | `IsWeakExpMetric d ξ D (fun r => r ^ (ξ * Q))`. |
| Q(ξ) | [`distExp d ξ`](../../HigherDimLQGMetric/Frozen/DistExp.lean#L28), [`IsDistanceExponent`](../../HigherDimLQGMetric/Frozen/IsDistanceExponent.lean#L32) | The Q for which log D_ε / log ε → 1 − ξQ in probability, for every admissible kernel and every white-noise realization of the band fields ([`IsLFPPExponent`](../../HigherDimLFPP/Frozen/IsLFPPExponent.lean#L23), [`IsBandVersion`](../../HigherDimLFPP/Frozen/IsBandVersion.lean#L23), [`IsWhiteNoise`](../../HigherDimLFPP/Frozen/IsWhiteNoise.lean#L24)). |
| the kernels of [1, Remark 1.1] | [`IsLFPPKernel κ`](../../HigherDimLFPP/Frozen/IsLFPPKernel.lean#L26), [`kernelSymbol`](../../HigherDimLQGMetric/Frozen/KernelSymbol.lean#L32), [`convKernel`](../../HigherDimLQGMetric/Frozen/ConvKernel.lean#L27), [`convKernelEps`](../../HigherDimLQGMetric/Frozen/ConvKernelEps.lean#L24) | κ is smooth, nonnegative, compactly supported and radial with ∫ κ² = 1; K̂(ζ) is the square root of the spherical-shell integral of the squared Fourier transform of κ beyond radius ‖ζ‖; K is its inverse Fourier transform and K_ε(x) = ε^{−d} K(x/ε). |
| h*_ε = h * K_ε | [`convMollify κ ε h z`](../../HigherDimLQGMetric/Frozen/ConvMollify.lean#L28) | The limit, as n → ∞, of the pairings of h with K_ε(z − ·) cut off radially at radius of order n ([`convTrunc`](../../HigherDimLQGMetric/Frozen/ConvTrunc.lean#L30)). The limit exists almost surely at every point (`convMollify_spec`). |
| D^ε_h | [`lfppDist κ ξ ε h (z, w)`](../../HigherDimLQGMetric/Frozen/LfppDist.lean#L29) | The infimum over piecewise C¹ paths P from z to w of ∫₀¹ e^{ξ h*_ε(P(t))} ‖P′(t)‖ dt ([`lfppDistOn`](../../HigherDimLFPP/Paths/DistOn.lean#L42)). |
| 𝔞_ε | [`aEps κ ξ ε`](../../HigherDimLQGMetric/Frozen/AEps.lean#L29) | The lower median of D^ε_h(0, e₁) under `normLGFLaw d`. |
| convergence in probability, locally uniformly | [`TendstoInProbLU P X l Y`](../../HigherDimLQGMetric/Frozen/TendstoInProbLU.lean#L29) | For all R, δ > 0, the outer probability that the supremum of the distance between X_i and Y over the product of the closed R-ball with itself is at least δ tends to 0 along l. |

## Correspondence with Theorems 1.2 and 1.4

- **Existence** (`theorem12`, first conjunct): an assignment D with `IsStrongExpMetric d ξ (distExp d ξ)
  D`, at Q = Q(ξ), the exponent the paper fixes in its standing hypotheses.
- **LFPP convergence** (same conjunct): for every admissible kernel κ, every probability space and every
  LGF plus a bounded continuous function h, `TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ
  ε (h ω)) (𝓝[>] 0) (fun ω => (D (h ω)).1)`. The limit is the same D for every kernel, as in the paper's
  Corollary 10.4, and ε tends to 0 through all real values. The median 𝔞_ε is the lower median; any other
  choice of medians has the same limit, because the point distance of the limit has full support (Lemma
  10.3, proved as [`lemma103`](../../HigherDimLQGMetric/Sec10/Lemma103.lean#L109)).
- **Uniqueness** (`theorem12`, second conjunct, and `strongUniqueness`): one deterministic constant C >
  0, chosen before the probability space, and one null set for all perturbations f and all endpoint
  pairs. This is the paper's wording; it is equivalent to the form with f = 0, because Weyl scaling
  commutes with constant multiples.
- **Theorem 1.4** (`theorem14`): the two assignments may have different normalizers c and c′; the
  conclusion is the same as for uniqueness.

## Scope and statement conventions

- **The exponent.** Theorem 1.2 is formalized at Q = Q(ξ) (ruling M12). The paper fixes Q = Q(ξ) in its
  standing hypotheses, and an assignment satisfying the four strong axioms at (ξ, Q) forces Q = Q(ξ): the
  sharp normalizers r^{ξQ} and r^{ξQ(ξ)} are both admissible only if they agree. Uniqueness for every Q >
  √(2d) is the separate theorem `strongUniqueness`.
- **The kernels.** The LFPP clause is proved for every nonnegative admissible white-noise kernel (ruling
  M6). The tightness theorem of [2], on which [1]'s construction rests, needs a nonnegative kernel; [1,
  Remark 1.1] also allows sign-changing kernels, for which no proof is available. The paper itself scopes
  the approximation clause to the kernels of [1].
- **The two LFPP-free theorems.** `theorem14Sharp` and `strongUniqueness` quantify over every Q > √(2d)
  (ruling M5). For subcritical ξ and Q ≠ Q(ξ) their hypotheses cannot be met, so they hold vacuously
  there; at Q = Q(ξ) they are inhabited by `sharpWeak_nonempty` and by the existence clause of
  `theorem12`.
- **Inputs and couplings.** An input is an LGF plus a random continuous function on the same probability
  space. The paper allows a coupling on another space; the two readings agree, because the joint law can
  be rebuilt on an extension of the original space and the axioms are statements about joint laws.
  Probability spaces range over Lean's `Type` universe. Locality (II) says that, almost surely, D_h(z, w;
  U) equals a fixed measurable function of h restricted to U, simultaneously for all z, w in U. The
  σ-algebra on distributions is generated by the pairings; it is the Borel σ-algebra of the weak
  topology, as in [1]. One normalizer family c serves every input; [1] lets it depend on the input, but
  the two readings define the same class, because two inputs differ by a continuous function whose weight
  is bounded on compact sets uniformly over the scales.
- **Junk values.** Lean's definitions are total. `sphereAvg` and `convMollify` are limits, and off the
  convergence set they take one fixed unspecified real; `sphereAvg_spec` and `convMollify_spec` show that
  the limits exist almost surely for every input. `distExp` and `normLGFLaw` are chosen when they exist
  (junk 0 otherwise); `distExp_spec`, `subcritical_nonempty` and `normLGFLaw_spec` show that they exist
  and are unique, so the choice is canonical. The independent statement audit traced every construct
  reachable from the statements that can take a junk value and found each either unreachable or excluded
  by one of the frozen theorems.
- **Dimension.** The theorems are stated for d ≥ 3, as in the paper. Several intermediate statements of
  the audits are false in dimension 0 or 1, where the sphere normalization degenerates or the sphere
  averages do not converge (rulings M21, M25–M28, M31); they are proved for d ≥ 1 or d ≥ 2, which is all
  the proofs use.
- **Constants.** In Lean the constant C is chosen before the probability space, the field and the
  perturbations, which is what "deterministic" means; it is provable because the constant depends only on
  the law of the field modulo constants.

## No assumptions: the literature inputs

The paper lists its imported results as (E1)–(E5) and cites eight works. Each is a theorem here or is not
needed:

| Paper's input | What the paper uses | In this release |
| --- | --- | --- |
| [1] Contreras Hip–Zhuang, Theorem 1.3, with [2] | (E1): every sequence ε_n → 0 has a deterministic subsequence along which 𝔞_ε⁻¹ D^ε_h converges to a weak assignment, also for an LGF plus a bounded continuous function | **proved** (block B3 below), for every nonnegative kernel: tightness, locality of the limits ([1, Lemma 3.11], [`l7a_locality_of`](../../HigherDimLQGMetric/Locality/Main.lean#L19)) through a Gaussian-projection decomposition of the field ([`dMarkovRd`](../../HigherDimLQGMetric/Markov/Main.lean#L20)), the comparison of two local metrics ([`l7d_bilip`](../../HigherDimLQGMetric/Bilip/Main.lean#L21)), determination by the field and one globally measurable assignment ([`b3Goal_of`](../../HigherDimLQGMetric/Thm13/Main.lean#L85); unconditionally [`b3Goal'`](../../HigherDimLQGMetric/Main/Inputs.lean#L55)) |
| [1] Theorem 1.6 | (E2): the weak normalizers can be taken to be r^{ξQ} | **proved** (block B4): every weak assignment has normalizers within constant factors of r^{ξQ(ξ)} and is weak with the normalizers r^{ξQ(ξ)} ([`theorem16`](../../HigherDimLQGMetric/Thm16/Theorem16.lean#L18); unconditionally [`theorem16Shape'`](../../HigherDimLQGMetric/Main/Inputs.lean#L59)), through the comparison of normalized LFPP with a weak assignment, [1, Proposition 4.2] ([`prop42`](../../HigherDimLQGMetric/Sec4/Prop42.lean#L47)) |
| [1] Propositions 3.13 and 4.6 | (E3): a bi-Lipschitz comparison of two weak assignments | **proved** in the sharp class ([`e3_sharp`](../../HigherDimLQGMetric/Sharp/E3.lean#L119), [`comparison_criterion`](../../HigherDimLQGMetric/Sharp/ComparisonCriterion.lean#L104)), with a corrected chaining step |
| [1] Lemma 2.7 | (E4): shell independence for local events | **replaced** by the paper's own Lemma A.1 ([`lemmaA1`](../../HigherDimLQGMetric/ShellDec/Tail.lean#L207)) and, for joint local metrics, its metric form ([`l7c_metricShell`](../../HigherDimLQGMetric/Bilip/MetricShell.lean#L154)); [1]'s route through an s-harmonic Markov property is not used |
| [1] Proposition 4.11 | (E5): moments of normalized internal diameters | **proved** in the sharp class ([`e5_sharp_moment`](../../HigherDimLQGMetric/Sharp/W3Tail.lean#L90)), with a new multiscale chaining proof in place of [1, Proposition 4.12] |
| [2] Ding–Gwynne–Zhuang, §§4–6 | tightness of LFPP in dimension d, behind (E1) and (E2) | **proved** (block B2, 170 files) on top of the [higher-dimensional LFPP release](../higher-dim-lfpp/), with its d-dimensional percolation duality repaired ([`realEpsAdapter`](../../HigherDimLQGMetric/DGZ/Adapter.lean#L19)) |
| [5] Krupski–Valov | a closed set of dimension at most d − 2 does not disconnect a connected open set | **replaced** by an elementary theorem for the sets that occur, at most two arcs in d ≥ 3 ([`ns_arc`](../../HigherDimLQGMetric/Topology/NonSep.lean#L207), [`ns_tree`](../../HigherDimLQGMetric/Topology/NonSep.lean#L219)) |
| [6] Contreras Hip–Zhuang, exponent bounds | kernel independence of Q(ξ) | **replaced** by a direct proof ([`kernel_indep`](../../HigherDimLQGMetric/KernelIndep/KernelIndep.lean#L157)); the existence of the exponent for each kernel is `HigherDimLFPP.exponent_exists` |
| [7] Chen–Dafnis–Paouris, Theorem 1(i) | the Gaussian Hölder inequality in Lemma A.1 | **proved** through the Ornstein–Uhlenbeck semigroup, in a whitened form that also covers degenerate blocks ([`gaussianHolder_prob`](../../HigherDimLQGMetric/Gauss/GaussianHolder.lean#L177)) |
| [3] Gwynne–Miller, [4] Ding–Gwynne, [8] Dubédat–Falconet | architecture and comparison only | **not needed**: the paper proves its own versions, and so does the formalization |

## How the proof is organized

The formalization has two phases, as planned before the statements were frozen. Phase A is the paper's
new argument (§§2–10 and Appendix A): uniqueness in the weak class with sharp normalizers, which needs no
LFPP. Phase B proves the inputs from [1] and [2], and the final assembly derives Theorems 1.2 and 1.4 as
in the paper's §10.

| Block | Paper | Directories | Main results | Lines |
| --- | --- | --- | --- | ---: |
| A1 fields | the LGF as a random distribution, sphere averages, Cameron–Martin, log-energy | `Field/`, `LGF/`, `Sphere/`, `CM/`, `LogEnergy/`, `WNSplit/` | [`exists_isWholeSpaceLGF`](../../HigherDimLQGMetric/LGF/Exists.lean#L223), `sphereAvg_spec`, `normLGFLaw_spec`, [`lgf_cameronMartin`](../../HigherDimLQGMetric/CM/Direction.lean#L426), [`lemma71`](../../HigherDimLQGMetric/CM/Holder.lean#L216) (Lemma 7.1), [`whiteNoiseSplit`](../../HigherDimLQGMetric/WNSplit/Split.lean#L103) | 15,366 |
| A2 metric geometry | §2: compactness, Hölder modulus, properness, measurable geodesics | `Metric/`, `Coord/`, `Config/`, `Select/`, `Proper/`, `Modulus/` | [`lemmaCC`](../../HigherDimLQGMetric/Coord/LemmaCC.lean#L23), [`configCompactFamily_isCompact`](../../HigherDimLQGMetric/Config/Family.lean#L42), [`lemma26_modulus`](../../HigherDimLQGMetric/Modulus/Lemma26.lean#L226) (Lemma 2.6), [`lemma27_proper`](../../HigherDimLQGMetric/Proper/Proper.lean#L27), [`exists_measurable_geodSelector`](../../HigherDimLQGMetric/Select/GeodSelector.lean#L90) | 15,248 |
| A3 topology | §4 input [5] | `Topology/` | `ns_arc`, `ns_tree` | 2,191 |
| A4 shell decoupling | Appendix A with [7] | `Gauss/`, `ShellDec/` | `gaussianHolder_prob`, `lemmaA1`, [`shellDecouplingFun_rd`](../../HigherDimLQGMetric/ShellDec/Bridge.lean#L78) | 4,160 |
| A5 sharp-class estimates | (E3), (E5), [1] §4 in the sharp class | `Shell/`, `Sharp/` | `e3_sharp`, `comparison_criterion`, `e5_sharp_moment`, [`internalDiam_le_of_multiscale`](../../HigherDimLQGMetric/Sharp/W3Multiscale.lean#L393) | 7,548 |
| A6 the new argument | §3 collapse; §4 routing and traps; §5 regular witnesses; §6 local traps; §7 change of measure; §8 counting; §9 closing | `Collapse/`, `Routing/`, `Trap/`, `Events/`, `Freq/`, `Amplify/`, `Sec6/`, `Sec8/`, `Sec8b/`, `Count/`, `ScaleBin/`, `Sec9/` | [`lemma31_collapse`](../../HigherDimLQGMetric/Collapse/Lemma31.lean#L17), [`lemma41_outer_routing_coordinates`](../../HigherDimLQGMetric/Routing/Lemma41OuterResult.lean#L219), [`lemma42_trap`](../../HigherDimLQGMetric/Trap/Lemma42.lean#L88), [`section5Package`](../../HigherDimLQGMetric/Freq/Package.lean#L61), [`fineFieldAmplification_of_lower_pair`](../../HigherDimLQGMetric/Amplify/Main.lean#L30), [`trapProps_of_stable`](../../HigherDimLQGMetric/Sec6/TrapStable.lean#L60), [`lemma81`](../../HigherDimLQGMetric/ScaleBin/Lemma81.lean#L24), [`lemma82`](../../HigherDimLQGMetric/Sec8/Lemma82.lean#L67), [`prop86`](../../HigherDimLQGMetric/Sec8b/Prop86.lean#L16) (Proposition 8.6), [`theorem14Sharp_of_parts`](../../HigherDimLQGMetric/Sec9/Closing.lean#L193) (§9, closing the gap) | 39,023 |
| A7 §10, Phase A part | Lemma 10.1, Corollary 10.2, Lemma 10.3 | `Sec10/` | [`lemma101`](../../HigherDimLQGMetric/Sec10/Lemma101.lean#L15), [`cor102Sharp_of`](../../HigherDimLQGMetric/Sec10/Cor102.lean#L20), `lemma103`, [`strongUniqueness_of`](../../HigherDimLQGMetric/Sec10/StrongUniq.lean#L18) | 3,248 |
| B1 [1] §2 | the kernel K, the convolution field, Lemmas 2.9–2.14, Proposition 1.10 | `Kernel/`, `ConvField/`, `Growth/`, `Trunc/`, `Law/` | `convKernel_smooth_integral`, `convMollify_spec`, [`l2a_sphereAvgGrowth`](../../HigherDimLQGMetric/Growth/Main.lean#L32), [`l2c_trunc`](../../HigherDimLQGMetric/Trunc/Main.lean#L23), [`l1e_law`](../../HigherDimLQGMetric/Law/Main.lean#L164) | 12,443 |
| B2 [2] §§4–6 | chaining, shells, concentration, FKG, comparison between scales, tightness, non-degeneracy | `DGZ/` | [`freeSiteLemma`](../../HigherDimLQGMetric/DGZ/FreeSites.lean#L80), [`boxSurgery`](../../HigherDimLQGMetric/DGZ/Fold.lean#L414), [`bypass`](../../HigherDimLQGMetric/DGZ/Bypass.lean#L593), [`cor52Shape`](../../HigherDimLQGMetric/DGZ/CompareCor52.lean#L87), [`distInfShape`](../../HigherDimLQGMetric/DGZ/TightExports.lean#L38), `realEpsAdapter` | 36,762 |
| B3 [1] §3 | Theorem 1.3: subsequential limits are weak assignments | `Weak/`, `LfppTight/`, `Limits/`, `Markov/`, `Local/`, `Locality/`, `Bilip/`, `Determ/`, `Thm13/`, `B3/` | [`l6c_lengthLimit`](../../HigherDimLQGMetric/Weak/DetLimit.lean#L211), `dMarkovRd`, [`l7b_copies_of_dim`](../../HigherDimLQGMetric/Local/CopiesMain.lean#L142), `l7c_metricShell`, `l7d_bilip`, [`l7e_measurable`](../../HigherDimLQGMetric/Determ/L7e.lean#L90), `b3Goal_of` | 40,179 |
| B4 [1] §4 and Q(ξ) | Theorem 1.6, Proposition 4.2, Lemmas 4.3–4.5; kernel independence | `KernelIndep/`, `Sec4/`, `Thm16/`, `B4/` | `kernel_indep`, `distExp_spec`, `subcritical_nonempty`, `prop42`, [`ref1_lemma43`](../../HigherDimLQGMetric/Sec4/Lemma43.lean#L275) (Lemma 4.3), `theorem16` | 9,522 |
| B5 assembly | Corollary 10.4, Theorems 1.2 and 1.4 | `Main/`, `Assembly/`, `Core/`, `Frozen/` | [`cor104_of_inputs`](../../HigherDimLQGMetric/Main/Cor104.lean#L189), [`theorem12_of_inputs`](../../HigherDimLQGMetric/Main/Theorem12.lean#L16), [`theorem14_of_inputs`](../../HigherDimLQGMetric/Main/WeakUniqueness.lean#L18), the unconditional inputs `b3Goal'` and `theorem16Shape'` | 3,528 |
| | | | **Total** | **189,218** |

The assembly follows the paper's §10. Theorem 1.4 combines Theorem 1.6 of [1] (every weak assignment is
sharp weak at Q(ξ)) with `theorem14Sharp`. Theorem 1.2 takes a subsequential LFPP limit (B3, with the
tightness input from B2), upgrades it to a strong assignment by Corollary 10.2, identifies the limit of
the full family by Lemma 10.3, and derives uniqueness from Lemma 10.1 and `theorem14Sharp`. The results
of [1] enter the assembly as unconditional theorems, collected in
[`Main/Inputs.lean`](../../HigherDimLQGMetric/Main/Inputs.lean): Theorem 1.3 (`b3Goal'`, from Lemmas 3.7,
3.11 and 3.16 of [1]), Theorem 1.6 (`theorem16Shape'`) and the paper's Lemma 10.3. The proof of
`theorem14Sharp` is the paper's §9: `theorem14Sharp_of_parts` closes the gap between the optimal
constants, using claim (32), which rests on Proposition 8.6.

## Differences from the paper

### Corrected statements

The proof follows a corrected rewrite of the paper and of its inputs ("blueprint", 142 pages), prepared
from independent section-by-section audits; its errata list has 185 items (82 for the paper, 58 for [1],
45 for [2]). While writing the proofs, the formalization found that several intermediate statements of
the paper or of the audits were false as written. Each was corrected by a recorded ruling, numbered as in
the development records that many source docstrings cite; none of them changed a frozen statement:

| Ruling | Statement | What was wrong | Correction |
| --- | --- | --- | --- |
| M15 | [S] Lemma 6.1, fine-field amplification; [S] Lemma 10.1, proof of tightness | with a compact set K_i of empty interior the amplified shape fails; in Lemma 10.1 only the weight bound holds for all scales at once | each K_i has nonempty interior ([`fineFieldAmplification_of_lower_pair`](../../HigherDimLQGMetric/Amplify/Main.lean#L30)); the other bounds of Lemma 10.1 are used for each scale separately, which suffices for tightness |
| M21 | the spectral Gram identity behind the kernel independence of Q(ξ) | false in dimension 0, where the natural-number power d − 1 degenerates | stated for d ≥ 1; every use has d ≥ 2 |
| M25 | [S] Lemma 7.1, the Cameron–Martin change of measure for fields normalized by their sphere average | false in dimension 0, where the sphere normalization does not fix the additive constant | stated for d ≥ 2; the form with mean-zero pairings keeps the original range |
| M26 | the σ-algebra identification behind [S] Lemma A.1 | false in dimension 1: the sphere averages do not converge and the junk value reveals an independent constant | stated for d ≥ 2 |
| M27 | Lemma R (regular events, [S] §5); the encoding of configurations | Lemma R is false in dimension 1 (the core annulus is disconnected); no encoding by continuous functions covers every metric | Lemma R for d ≥ 2; two encodings, bridged on the almost sure event where the metrics are length metrics |
| M28 | [S] Lemma 10.1: a strong assignment is weak with normalizers r^{ξQ} | false in dimension 1, by the one-dimensional exponential metric of the field | stated for d ≥ 2 |
| M29 | [S] Lemma 2.6, the Hölder modulus | an untyped exponent was read as a natural number, which claims an integer decay rate that fails near the threshold | the exponent is real (`lemma26_modulus`); the natural-number form holds in a smaller range |
| M30 | the interface between the tightness input ([2]) and the existence proof ([1] §3) | the box-median tightness statement planned as the interface is not what [2]'s proof produces | the interface is the real-ε tightness statement that [2]'s proof yields (`realEpsAdapter`) |
| M31 | joint locality of conditionally independent copies ([1] §3) | the proof needs the field to be recoverable from its recentred version, which uses convergent sphere averages; no counterexample in dimension 1 is known | stated for d ≥ 2, which every use satisfies |
| M32 | an intermediate statement for the deterministic part of [S] Proposition 6.2 (not the paper's wording) | an alternate bump supported far from the annulus changes the discount near the trap (explicit counterexample) | the bumps of every label are supported in the annulus A_{1,3}, as the trap families of §6 provide (`trapProps_of_stable`) |
| M33 | the median normalization of [2]'s Hölder tightness (Corollary 5.2 to Proposition 6.3) | the upper bounds of Lemmas 6.1–6.2 do not control the median without a lower tail (explicit counterexample) | the comparability (6.5) of [2] is proved from its Proposition 6.4 and used explicitly |
| M37 | [1] Lemma 4.3, a lower bound on the probability of a good event at every scale 0 < ε < r < 1, proved through a localized field | the transfer to the localized field fails as ε tends to 1: the localization radius tends to 0, so the localized field at a point has diverging variance while the field stays tight | proved for ε below a fixed ε₀ (`ref1_lemma43`), which is all that Lemmas 4.4 and 4.5 and Proposition 4.2 use |
| M38 | [1] Remark 3.8 for a field plus a continuous function, as completed by the audit: the limits are proper metrics | false for unbounded functions: with f(x) = −‖x‖² and the Euclidean metric, a ray has finite weighted length, so the weighted metric is not proper | the limits are continuous metrics inducing the Euclidean topology, which is all the weak class asks; properness is not used |

Further corrections of the same kind: deterministic rescaling of sphere averages holds only for dyadic
factors, and almost surely for the field (M17); the multiscale diameter bound needs grid radius ρ_n/64,
and [1, §4.1]'s localization is used only for small ε (M18); Weyl scaling is continuous in the weight in
the forms that are true (M19); [S] Lemma 2.5 needs finite distances on the confinement set (M22); two
statements that the audit of [2] had omitted, ξ(Q − √(2d)) ≤ 1 (which [2] takes from its Lemma 3.7) and
Lemma 6.7 for perturbed fields, are proved (M23); the events of [S] §8 are replaced by Borel versions
that agree with them almost surely (M34).

### Gaps repaired

The audits found no false step in the paper's own argument (§§1–10 and Appendix A); its minor gaps were
repaired with full proofs. The main ones: Theorem 1.2 with Q left free is false for Q ≠ Q(ξ) (hence
ruling M12); the reduction to sharp normalizers is used but never stated; the version of Lemma 2.2 that
is used, the confinement hypothesis of Lemma 2.5, the grid covering of Lemma 2.6 and the measurable
selection of geodesics needed proofs; Proposition 6.2 is proved in the stronger deterministic form that
§8 needs.

In the imported works the audits found serious gaps, all repaired:

- **[2], the percolation duality.** The d-dimensional duality step is used at nine places without proof.
  It is proved with the percolation surgery of the [higher-dimensional LFPP
  release](../higher-dim-lfpp/), new free-site and hole lemmas, box surgery by folding and a new
  threshold min(r₂, r₁ − r₂)/16.
- **[1, Proposition 4.12].** The diameter moments (E5) were derived from a planar crossing argument that
  fails in d ≥ 3; they are proved by a new multiscale chaining, with the same exponent.
- **[1, Proposition 3.13].** The chaining claim fails when a sphere is swallowed by a later, larger ball;
  it is repaired by a stack argument.
- **[1, Proposition 3.15], Step 4.** An Efron–Stein bound was applied on a random event; it is replaced
  by a bound through boundary boxes.
- **[1, Theorem 1.3], Step 3.** No globally defined measurable assignment was constructed for unbounded
  perturbations; one is built by a local chain construction.
- **[1, Lemma 3.3].** A coupling claim is false; it is not needed.
- **[6, Remark 1.1]** is a sketch about a different exponent; the kernel independence of Q(ξ) is proved
  directly.
- **[7].** The proofs normalize the diagonal blocks, which presupposes non-degenerate blocks; the
  inequality is proved in a whitened form.

### Not formalized

- The LFPP clause for sign-changing kernels (see above), and tightness for other mollifiers, which the
  paper does not claim.
- Existence at Q ≠ Q(ξ), which is false.
- [1]'s route to locality through the s-harmonic Markov property, [5] beyond at most two arcs, and [6]
  beyond kernel independence and the bound Q(ξ) ≥ 1/ξ − √(2d) that gives `subcritical_nonempty`.
- The correspondence γ = Q − √(Q² − 2d), which the paper uses only as notation, and numerical values of
  the constants.

## How the statements are pinned

- **Frozen statement surface.** The 57 statements (46 definitions and 11 theorems) were written one
  declaration per file before any proof, and audited independently against the paper: each theorem type
  was reconstructed from the paper and found syntactically identical to the frozen one, with no
  hypothesis beyond the paper's and those of rulings M5 and M6. A manifest records, for every
  declaration, a hash of its elaborated type and definition body and a hash of its file; a fingerprint
  covers the 168 non-Mathlib constants that the statements reach, and the 18 upstream files they use are
  pinned by hash. At every seal these were recomputed and found unchanged.
- **Two-key seals.** Each theorem was sealed twice: first by mechanical checks (only the proof body
  changed, the manifest guard passes, the statement hashes are identical, the build is fresh, the axioms
  are standard), then by an independent audit, run by a different model than the one that wrote the proof
  wherever possible, which also reviewed the proof route for hypothesis smuggling and junk values. The
  statement audit also required that the main theorems count as proved only once the six characterization
  theorems and `sharpWeak_nonempty` are sealed, so that the definitions mean what the paper means and the
  weak class is inhabited; all eleven are sealed. Seals: five batches of key 1 and the independent audits
  A-seal-1 to A-seal-5, all PASS.
- **Axioms.** `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for each of the eleven
  theorems, and the certificates below traverse every declaration of the included libraries. No `sorry`,
  `admit`, custom `axiom` or unsafe declaration occurs in the shipped sources (checked by the public
  source scan), and the axiom audits would reject `native_decide`, whose proofs depend on an extra axiom.
- **Kernel replay.** `leanchecker --fresh` re-checked every declaration of the closure, Mathlib included,
  in a fresh environment (exit code 0 on 22 October 2026, 01:45–01:53 CEST, in 8 min 5 s, on the Lean
  sources of commit `22770ff22`).

## Dependencies

The library reuses earlier releases of this repository; none of their modules changes.

| Library | Modules in the closure | What this release uses |
| --- | ---: | --- |
| HigherDimLQGMetric (new) | 1,310 | this formalization |
| [HigherDimLFPP](../higher-dim-lfpp/) | 96 | ℝ^d, e₁, white noise and band fields, admissible kernels, LFPP paths and distances, the existence of the exponent for each kernel, percolation surgery |
| [LQGMetric](../lqg-metric/) | 535 | metric geometry (internal metrics, length spaces, geodesics), probability and measurability tools, the planar arguments that the d-dimensional ones port |
| [QuantumZipper](../quantum-zipper/) | 733 | Cameron–Martin shifts and laws of Gaussian vectors (directly and through LQGMetric) |
| [LQGDimension](../small-gamma-dimension/) | 36 | the Gaussian integration-by-parts lemma used for the Gaussian Hölder inequality |
| [GaussianLQG](../gaussian-lqg-distance/) | 10 | Gaussian moments, medians and white-noise realizations |

Lean is `v4.34.0-rc2` and Mathlib is `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`, as for the rest of the
repository.

## Verification

The export adds **1,310 modules**, the `HigherDimLQGMetric` modules of the closure (189,218 lines),
copied byte-for-byte from development commit `22770ff221dba08ca55daf25606b31f5c6b4b8cb` (the release
commit; the last two frozen theorems were sealed in `014982b3d`, and the exported files are the same at
both commits). The local import closure of the eleven frozen theorems has **2,720 modules**: 1,310
HigherDimLQGMetric, 535 LQGMetric, 733 QuantumZipper, 96 HigherDimLFPP, 36 LQGDimension and 10
GaussianLQG. The other 1,410 were already part of this release and are byte-identical.

- **Kernel replay (development workspace).** `lake env leanchecker --fresh` on a module that imports the
  eleven frozen theorem modules re-checked, in a fresh environment, every declaration of their closure,
  Mathlib included: exit code 0 on 22 October 2026, 01:45–01:53 CEST, in 8 min 5 s, on the Lean sources
  of commit `22770ff22`.
- **Fresh build and focused certificate (this export).** The 1,310 new modules were **compiled afresh
  from the exported files**, with the public verifier's per-module settings (`lean -j1 -M8192`): 2,400
  seconds of wall time, at most 59.8 seconds and 4.9 GB per module. The 1,410 previously released
  dependencies were reused after all closure files were checked byte-for-byte. [`Check.lean`](Check.lean)
  was then compiled afresh and **passed**. It checks the verbatim statements of the eleven theorems,
  derives that their hypotheses can be met, prints the main definitions, and checks the literature inputs
  and the section-level results. It rejects `sorry` and audits **37,667 project declarations and 121,818
  reachable declarations**, allowing only `propext`, `Classical.choice` and `Quot.sound`. See
  [verification.json](verification.json). `leanchecker --fresh` then replayed this build: exit code 0 (7
  min 53 s), through a scratch module that imports the eleven frozen theorem modules.
- The [public workflow](https://github.com/leobon12/lean-formalizations/actions/workflows/verify.yml)
  rebuilds every module from source and runs the combined [certificate](../../Certificate.lean), which
  includes these theorems.

To reproduce from the public repository:

```sh
lake exe cache get
lake build HigherDimLQGMetric.Frozen.Theorem12 HigherDimLQGMetric.Frozen.Theorem14 \
  HigherDimLQGMetric.Frozen.Theorem14Sharp HigherDimLQGMetric.Frozen.StrongUniqueness \
  HigherDimLQGMetric.Frozen.SharpWeakNonempty HigherDimLQGMetric.Frozen.DistExpSpec \
  HigherDimLQGMetric.Frozen.SubcriticalNonempty HigherDimLQGMetric.Frozen.NormLGFLawSpec \
  HigherDimLQGMetric.Frozen.ConvKernelSmoothIntegral HigherDimLQGMetric.Frozen.SphereAvgSpec \
  HigherDimLQGMetric.Frozen.ConvMollifySpec
lake env lean results/higher-dimensional-lqg-metric/Check.lean
for m in Theorem12 Theorem14 Theorem14Sharp StrongUniqueness SharpWeakNonempty DistExpSpec \
    SubcriticalNonempty NormLGFLawSpec ConvKernelSmoothIntegral SphereAvgSpec ConvMollifySpec; do
  lake env leanchecker --fresh HigherDimLQGMetric.Frozen.$m
done
```

`Check.lean` runs `#print axioms` on each theorem; the expected output is `[propext, Classical.choice,
Quot.sound]`. `leanchecker --fresh` accepts a single module, hence the loop; each run replays Mathlib as
well. The first two modules already cover the two main theorems with their whole proofs.

The sources are published byte-for-byte. Their docstrings cite development documents that are not part of
this snapshot: the corrected rewrite ("blueprint"), rulings (such as M12 above), audits, work packets and
the frozen-anchor manifest. Kernel checking establishes the Lean proofs; correspondence with the paper is
the subject of the conventions above.

## Credits

The paper builds on Contreras Hip–Zhuang [1] (arXiv:2512.06292) and [6] (arXiv:2504.09141),
Ding–Gwynne–Zhuang [2] (arXiv:2310.03996), Gwynne–Miller [3] (arXiv:1905.00383), Ding–Gwynne [4]
(arXiv:2110.00177), Krupski–Valov [5] (arXiv:0901.1329), Chen–Dafnis–Paouris [7] (arXiv:1306.2410) and
Dubédat–Falconet [8] (arXiv:1809.02607). The formalization reuses the [higher-dimensional
LFPP](../higher-dim-lfpp/), [LQG metric](../lqg-metric/), [Gaussian LQG
distance](../gaussian-lqg-distance/), [small-parameter LQG dimension](../small-gamma-dimension/) and
[Quantum Zipper](../quantum-zipper/) releases. The original mathematical results are due to their
authors; source-file attribution is retained. The statements were frozen and audited following Scott
Armstrong's [LeanAutoformalizationSkills](https://github.com/scottnarmstrong/LeanAutoformalizationSkills)
workflow.

[All released formalizations](../../README.md)
