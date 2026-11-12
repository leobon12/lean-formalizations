# Liouville Brownian motion and quantum cones in dimension $d>2$

The Lean formalization covers all five named main results of Federico Bertacco and Ewain Gwynne’s paper, together with the subcritical construction of Liouville Brownian motion (LBM) from every starting point. The project also proves an identification with the Duplantier–Miller–Sheffield planar quantum cone. The formulations of Theorems D and E are specified below. [Bertacco–Gwynne, arXiv:2501.15936v2](https://arxiv.org/abs/2501.15936v2)

## Theorems A–E

Write $Q=d/\gamma+\gamma/2$ and $\alpha=Q-\sqrt{Q^2-4}$. For the subcritical LBM results, $0<\gamma<\sqrt{2d}$.

| Theorem | What the Lean declaration proves |
| --- | --- |
| **A** · Spherical averages | In even $d\ge4$, identifies the spherical-average process and its derivatives via the stationary Gaussian Markov process and the moving-average representation. A companion theorem identifies the planar radial process with two-sided Brownian motion. |
| **B** · Spectral dimension | For $d\ge2$ and $\beta<Q$, the spectral dimension at the origin of the field $h-\beta\log\lvert\cdot\rvert$ is $2+2(d-2)/(2+\alpha^2/2-\alpha\beta)$. Lean uses the paper’s Brownian-bridge moment definition and identifies the moments with integrated heat-kernel densities almost everywhere in the endpoint. In the plane the dimension is $2$. |
| **C** · Radial part of the cone | In even $d\ge2$, the radial law seen from first passage converges in total variation on every half-line $[T,\infty)$. Lean identifies the limiting law used to construct the cone. |
| **D** · Cone as a local limit | The rescaled field converges in total variation on every fixed ball. At a zoom center $z$, Lean first subtracts $h_1(z)$. This agrees with the printed normalization at $z=0$. The result at $z\ne0$ with the original normalization at the origin is outside the verified claim. |
| **E** · Invariance along LBM | For the $\alpha$-cone in even $d\ge2$, the recentered field and two-sided path have the original joint law after the canonical spatial rescaling. The path is $s\mapsto R_t^{-1}(X_{t+s}-X_t)$, with time shifted as well as space. This corrects the displayed path in the paper and puts the new root at the origin at time zero. |

The Lean names are `theoremA` through `theoremE`. `coneClock` constructs the cone clock, including at the marked origin. `theoremF` identifies the two-dimensional cone with the Duplantier–Miller–Sheffield construction for $\beta<Q$. [Statements of A–E in the paper](https://arxiv.org/html/2501.15936v2#S2) · [Lean inspection file](PaperResults.lean)

## Construction of subcritical LBM

Let $h$ be a whole-space log-correlated Gaussian field normalized by $h_1(0)=0$, and let $B$ be an independent standard Brownian motion started from $x$. Write $h_\varepsilon$ for the spherical average of $h$ at radius $\varepsilon$. Set $Q=d/\gamma+\gamma/2$ and $\alpha=Q-\sqrt{Q^2-4}$. For each fixed start, the regularized clocks

$$
F_\varepsilon(t)=\int_0^t \varepsilon^{\alpha^2/2}\exp\!\bigl(\alpha h_\varepsilon(B_s)\bigr)\,ds
$$

converge in probability, uniformly on bounded time intervals, under the joint law of the field and the Brownian motion. Their limit $F$ is a positive continuous additive functional with Revuz measure $\mu_{h,\alpha}$, the field’s Gaussian multiplicative chaos. **For almost every field, for every starting point $x$**, the clock is almost surely finite at finite times, continuous, strictly increasing from zero, and tends to infinity. Its inverse gives the path

$$
X_t=B_{C_t},\qquad C_t=\inf\{s\ge 0:F(s)>t\}.
$$

In dimension two, $\alpha=\gamma$ and $h_\varepsilon$ is the circle average of the whole-plane Gaussian free field. Thus the construction includes $\sqrt{2}\le\gamma<2$, beyond the planar second-moment range. It gives a strong Markov process from every point, symmetric with respect to $\mu_{h,\gamma}$, with a transition density against that measure at every positive time. In higher dimensions the all-start theorem here has $Q>\sqrt{2d}$. The paper also discusses the range $2<Q\leq\sqrt{2d}$ with a Brownian-polar exceptional set of starting points. [Bertacco–Gwynne, §5](https://arxiv.org/html/2501.15936v2#S5)

## Where the mathematics enters Lean

| Mathematical step | Declaration in `LBMHigherDim` |
| --- | --- |
| The Euclidean Wiener law has independent standard Brownian coordinates | `isBrownian_euclideanWienerLaw` |
| The canonical measure is the spherical-average GMC of the field | `isGMCOf_canonGMC` |
| The strict clock and its Revuz identity | `lbm_a1`, `lbm_a2` |
| Finiteness, strict increase and divergence from every start | `lbm_a4` |
| Convergence of the field-regularized clock above | `lbm_a6` |
| The inverse-clock path identity, Feller property, and symmetry | `lbm_a7` |
| Strong Markov property on canonical path space and existence of the heat kernel | `lbm_a7_canonical`, `lbm_a8` |

The quantifier order appears directly in the statement of `lbm_a4`. Here `P` is the field law and `bm x` is Wiener measure started at `x`.

```lean
theorem lbm_a4 (hγ : Subcritical d γ) (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ x, ∀ᵐ b ∂(bm x), pcafClock (lbmGMC d γ (h ω)) b 0 = 0 ∧
      (∀ t, pcafClock (lbmGMC d γ (h ω)) b t ≠ ⊤) ∧ Continuous (pcafClock (lbmGMC d γ (h ω)) b) ∧
      StrictMono (pcafClock (lbmGMC d γ (h ω)) b) ∧ Tendsto (pcafClock (lbmGMC d γ (h ω)) b) atTop (𝓝 ⊤)
```

## Which planar results of Garban–Rhodes–Vargas are covered?

The formalization establishes the following counterparts for the **massless whole-plane GFF with unit-circle average zero**, for every $0<\gamma<2$. GRV’s principal planar model is a **massive GFF** with covariance given by the Green function of $m^2-\Delta$, $m>0$. Fixing the additive constant of the massless field does not turn one covariance into the other. A separate theorem would be needed to carry the results to GRV’s model. [GRV, §§2.1–2.2](https://arxiv.org/pdf/1301.2876v4#page=3)

| GRV result | Coverage in the normalized whole-plane model |
| --- | --- |
| **Theorem 2.7** · Clock | `lbm_a1`–`lbm_a5` give the strict clock, uniqueness via its Green martingale, the Revuz identity, approximation, strict increase, divergence and continuity in the starting point. `lbm_a3_gs` supplies a concrete approximation for the quenched statement. `lbm_a6` identifies the circle-average clock in probability under the joint field and Brownian law. The specific massive-field regularization in GRV is outside this identification. |
| **Definition 2.17, diffusion assertion of Theorem 2.18, Proposition 2.19(1), Corollary 2.20** | `lbm_a7` and `lbm_a7_canonical` identify the inverse-clock process from every start, give continuous paths and the strong Markov property, and prove symmetry and continuity of the path law in the start. The semigroup maps bounded continuous functions to bounded continuous functions. |
| **Theorem 2.10** · Clock moments | GRV prove finiteness up to $q<4/\gamma^2$ and a power-law bound on positive moments of clock increments. The project proves the moment estimates needed for Bertacco–Gwynne. Its proved targets do not include GRV’s full massive-field clock increment estimate. |
| **Theorems 2.18(2) and 2.21** | GRV also prove that the associated Dirichlet form is regular and strongly local with $C_c^\infty$ as a special core, and a joint limit in which the regularized SDE’s driving Brownian motion is independent of the limiting LBM. Neither conclusion appears among this project’s proved targets. The field–Brownian independence used to construct the clock is a different statement. |

**Why the planar hypotheses have a witness.** `HigherDimLQGMetric.exists_isWholeSpaceLGF` constructs a field from white noise. `isProbabilityMeasure_normLGFLaw` and `isNormalizedLGF_normLGFLaw` show that `normLGFLaw 2` is a probability measure and that the identity field under it satisfies `IsNormalizedLGF`. Taking, for example, $\gamma=3/2$ gives an instance beyond the planar second-moment range. `lbm_a4` then gives a strictly increasing, divergent clock for every starting point on one full-field-probability event. The general approximation lemma has hypotheses on the approximating sequence, while the final clock and path theorems take only subcriticality and the field law as mathematical hypotheses. [Lean witness for the normalized field](../../HigherDimLQGMetric/Frozen/NormLGFLawSpec.lean) · [GRV, Theorem 2.7](https://arxiv.org/pdf/1301.2876v4#page=10) · [GRV, Theorems 2.18–2.21](https://arxiv.org/pdf/1301.2876v4#page=24)

GRV also include $\gamma=0$ and discuss the sphere, torus and bounded domains. The coverage above is for positive $\gamma$ on the whole plane. A complete formalization of GRV would also have to address the model and theorem gaps above.

## Size and verification

The paper-specific library contains **85,302 lines in 659 Lean files**, including the root import file. Of those, **64,109** are nonblank lines containing code after comments are removed. These counts exclude Mathlib and all shared project libraries. The narrower construction imports 369 files from the paper library (46,310 lines).

The source audit at revision `1cb4634e` checked the pinned declarations and dependency hashes. Lean independently checked the planar identity $\alpha(2,\gamma)=\gamma$ against the pinned Mathlib revision. The development record reports a successful full kernel replay with Lean 4.34.0-rc2 and only `propext`, `Classical.choice`, and `Quot.sound` for the sealed theorems. The full kernel replay is the project’s recorded check.

The public folder provides the result guide and Lean inspection files. Running them requires `GMCTilings` and `ParameterizedWalk`, two private development libraries. [Main results and field witness](PaperResults.lean) · [LBM construction](LBMConstruction.lean) · [Definition of the whole-space field](../../HigherDimLQGMetric/Frozen/IsWholeSpaceLGF.lean)
