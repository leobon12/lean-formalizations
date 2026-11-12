# Subcritical Liouville Brownian motion in dimensions $d\ge 2$

The Lean result constructs Liouville Brownian motion (LBM) on the whole space $\mathbb R^d$ for every integer $d\ge 2$ and every $0<\gamma<\sqrt{2d}$. It covers the full planar range $0<\gamma<2$. The source is Federico Bertacco and Ewain Gwynne, *Liouville Brownian motion and quantum cones in dimension $d>2$*, equation (2.5), Definition 2.4, Proposition 2.5 and Theorem 5.12, together with the planar construction of Garban, Rhodes and Vargas. [Bertacco–Gwynne, §2.2](https://arxiv.org/html/2501.15936v2#S2.SS2) · [Garban–Rhodes–Vargas](https://arxiv.org/abs/1301.2876)

## The process

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

## Verification and source access

The result was developed in Lean 4.34.0-rc2 with Mathlib at `a4c8ef0a`. The source audit at revision `1cb4634e` traced the declarations to their proofs and checked the pinned definitions and dependency hashes. The development record reports a successful full Lean kernel replay and lists only `propext`, `Classical.choice`, and `Quot.sound` for the sealed theorems.

This public folder contains the result guide and a Lean file that prints the clock and path theorems and their axiom dependencies. Running it requires the development libraries `GMCTilings` and `ParameterizedWalk`, which are private. [Lean inspection file](LBMConstruction.lean) · [Whole-space field definition](../../HigherDimLQGMetric/Frozen/IsWholeSpaceLGF.lean) · [Euclidean Wiener law](../../BouRabeeGwynne/EuclideanWienerLaw.lean)
