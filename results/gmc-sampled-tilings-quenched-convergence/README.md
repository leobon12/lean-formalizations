# Quenched convergence of GMC-sampled tilings

**Theorem 1.1 is formalized in all dimensions $d\ge 3$, for the full parameter range in (1.1) of the October 11, 2026 manuscript.** This includes $d=3$. The result concerns the conductance random walk on Euclidean Voronoi cells sampled from the Gaussian multiplicative chaos (GMC) of a quantum cone. [Manuscript, Theorem 1.1](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/gmc-sampled-tilings-quenched-convergence.pdf)

## The limit theorem

Take $0<\gamma<\sqrt{2d}-\sqrt{2d-1}$, set $Q=d/\gamma+\gamma/2$ and $\alpha=Q-\sqrt{Q^2-4}$, and let $h$ be an $\alpha$-quantum cone. Conditional on $h$, the nuclei form a Poisson process of intensity $\varepsilon^{-1}\mu_{h,\gamma}$. The walk starts at the nucleus whose cell contains the origin. A shared facet gives its two nuclei conductance equal to the facet’s area divided by the distance between them.

The deterministic duration of each step is $2\varepsilon^{\alpha/\gamma}/Z$. Lean proves that the normalizing constant satisfies $0<Z<\infty$. As $\varepsilon\downarrow0$, the conditional law of the interpolated walk converges in probability to the law of $\alpha$-Liouville Brownian motion in the same field, started at the origin. This holds both when conditioning on the field and the nuclei and when conditioning on the field alone. Interpolated paths use the topology of uniform convergence on compact time intervals. The step paths have the corresponding limits in the local Skorokhod $J_1$ topology.

## Lean statement and proof

| Declaration | Role |
| --- | --- |
| `GMCTilings.Theorem11Statement` | Specifies the admissible range, random environment, finite positive normalizer and four convergence statements. |
| `GMCTilings.theorem11` | Proves that statement. Its proof uses `GMCTilings.Environment.theorem11_proof`, which supplies the required environment estimates. |
| `GMCTilings.NV.theorem11_hypotheses_satisfiable_of_inRange` | Constructs a model for every admissible pair $(d,\gamma)$. The library also gives the explicit example $d=3$, $\gamma=1/12$. |

The development uses the record-Palm construction of the cone. A separate theorem identifies its radial law with the paper’s first-passage law whenever the latter exists. The odd-dimensional first-passage limit is also proved in the LBM development. [Odd-dimensional cone results](../odd-dimensional-fields-and-quantum-cones/)

The source revision is `8171c033` of the private research repository. Its verification record reports a successful full kernel replay and only `propext`, `Classical.choice` and `Quot.sound` for the main theorem. The public folder contains this guide and inspection commands. To run them, use the original `GMCTilings` workspace and its private `ParameterizedWalk` dependency with Lean 4.34.0-rc2. [Lean inspection file](Check.lean)
