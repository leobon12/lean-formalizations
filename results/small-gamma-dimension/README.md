# Small-parameter asymptotics for the LQG dimension

Lean companion to **Theorem 1.1 and Proposition 1.2** of *Small-parameter asymptotics for the
Liouville quantum gravity dimension*, September 21, 2026, developed under Leonardo Bonanno's
direction with AI assistance. The source statement matches the 17-page
[research manuscript](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/small-gamma-lqg-dimension.pdf),
including the LFPP model, covariance normalization, variational coefficient, and explicit
literature inputs described below.

[Exact statements](../../LQGDimension/Statement/Main.lean) ·
[Definitions](../../LQGDimension/Statement/Defs.lean) ·
[Proof](../../LQGDimension/Assembly/Theorem11.lean) ·
[Focused certificate](Check.lean) · [Verification record](verification.json)

## Results

Let h be the whole-plane GFF with h₁(0) = 0 and logarithmic covariance singularity
log|z − w|⁻¹. Let D^ξ_ε be the infimum of the circle-average LFPP length
∫ exp(ξ h_ε(z)) |dz| over piecewise C¹ paths from 0 to 1 in U = (−2,2)², with arclength
counting multiplicity. An LFPP exponent λ(ξ) means log D^ξ_ε / log ε → λ(ξ) in probability
as ε ↓ 0.

The coefficient is defined by a Gaussian variational problem. Let V_n consist of the continuous
functions on [0,1] which vanish at both endpoints and are affine on the uniform mesh 16⁻ⁿ.
For the centered Gaussian process Z with covariance

> Cov(Z_f,Z_g) = π ∫₀¹ (|f| + |g| − |f − g|) dx,

set E(f) = ½∫₀¹ |f′|² dx and a_n = E sup_{f∈V_n}(Z_f − E(f)). The Lean definition expresses
this expectation as the supremum of expected maxima over finite subfamilies, matching the
separable continuous Gaussian version in the manuscript.

| Result | Lean declaration |
| --- | --- |
| Every a_n is finite, (a_n) is subadditive, and 0 < a* = lim a_n/n = inf_{n≥1} a_n/n < ∞. | [`theorem11_aStar`](../../LQGDimension/Assembly/AStarProved.lean) |
| If LFPP exponents exist for all ξ in some interval (0, ξ₀), then λ(ξ)/ξ^(4/3) → a*/log 16 as ξ ↓ 0. | [`theorem11_lambda`](../../LQGDimension/Assembly/Theorem11.lean) |
| If d_γ → 2 and the exponent relation λ(γ/d_γ) = 1 − (2 + γ²/2)/d_γ holds for all sufficiently small γ > 0, then (d_γ − 2)/γ^(4/3) → 2^(−1/3)a*/log 16. | [`theorem11_dimension`](../../LQGDimension/Assembly/Theorem11.lean) |
| All three assertions together. | [`theorem11`](../../LQGDimension/Assembly/Theorem11.lean) |
| The two finite-block bounds in Proposition 1.2, in an exponent-free form. | `prop12Upper`, `prop12Lower` in the same import closure |
| A probability space carrying a GFF circle-average process with the specified covariance and continuity exists. | [`gffCircleAverageExists`](../../LQGDimension/Existence/Assembly.lean) |

The limit coefficient is characterized variationally; no numerical value or closed-form evaluation
is claimed.

## Scope and correspondence

The LFPP-exponent existence hypothesis and the two hypotheses on d_γ are **explicit inputs** of
the formal theorem. They correspond to facts imported from the literature in the manuscript.
The formalization proves the small-parameter implication for every function d satisfying these
facts. It does not construct the canonical LQG metric or prove, inside this particular theorem,
that its intrinsic Hausdorff dimension satisfies them. The separately released LQG metric work
is not silently substituted for these hypotheses.

All probability spaces range over Lean's `Type` universe. Gaussianity, mean zero, exact
circle-average covariance, and spatial continuity are specified by `IsGFFCircleAverage`.
The existence proof above supplies an actual witness to this field predicate. The variational
Gaussian covariances are proved positive semidefinite, and LFPP distances are positive; the
relevant infima and Gaussian laws are not default-value substitutes.

The circle-average regularization, fixed endpoints 0 and 1, domain U, constants 4/3, 2^(−1/3),
and log 16 agree with the manuscript. Its additional continuity and monotonicity statements
about γ/d_γ are not required by the Lean dimension implication. This release does not claim a
formal proof of unrelated odd-dimensional cone, SDP, higher-dimensional metric, or supercritical
conformal-covariance results.

**Update (19 October 2026).** The [higher-dimensional LFPP release](../higher-dim-lfpp/) discharges these
inputs in separate theorems. `HigherDimLFPP.gff_circle_average_lfpp` proves, for every
`IsGFFCircleAverage` process, that the LFPP exponent exists for all small ξ and that
λ(ξ)/ξ^(4/3) → κ₂: this is `theorem11_lambda` without its existence hypothesis.
`HigherDimLFPP.lqg_dimension_asymptotics` proves (d_γ − 2)/γ^(4/3) → 2^(−1/3)κ₂ for the LQG dimension
`LQGMetric.dGamma`, and `HigherDimLFPP.kappa_two_eq` gives κ₂ = a*/log 16. The statements above are
unchanged.

## Verification

The export adds **8 modules**, with **107 existing public modules reused without changing a
byte**, for a **115-module** local import closure. Every exported source file matches the
current upstream source and the available compiled checkout byte-for-byte. The compiler and
Mathlib pins agree with the public project: Lean `v4.34.0-rc2`, Mathlib
`a4c8ef0a69f52ec80525d5086bb3542f4660faaf`.

The focused certificate **passed** after being compiled afresh against these matching cached proof modules.
It checked the named statement types, rejected `sorry`, and traversed **4,418 project declarations**
and **69,331 reachable declarations**, allowing only `propext`, `Classical.choice`, and
`Quot.sound`. See [verification.json](verification.json) for the result. This is an incremental
certificate check, not a fresh compilation or kernel replay of every dependency.

To reproduce from the public repository:

```sh
lake exe cache get
lake build LQGDimension.Assembly.Theorem11 LQGDimension.Existence.Assembly LQGDimension.Sanity
lake env lean results/small-gamma-dimension/Check.lean
```

The source-to-paper comparison and explicit hypotheses above are separate from the kernel's
verification of the Lean declarations.

[All released formalizations](../../README.md)
