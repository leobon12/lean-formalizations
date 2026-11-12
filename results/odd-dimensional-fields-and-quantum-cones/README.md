# Odd-dimensional fields and quantum cones

**Partial formalization.** The Gaussian moving-average identity (2.3) from Theorem A and the two quantum-cone limits, Theorems B and C, have Lean proofs that apply in odd dimensions. The consolidated manuscript also treats the Fourier spectrum, sharp regularity and a Markov representation of the Brownian memory. Those statements are outside the verified coverage of this guide. [October 11, 2026 manuscript](https://github.com/leobon12/ai-generated-mathematics/blob/main/papers/odd-dimensional-fields-and-quantum-cones.pdf)

## Verified statements

| Manuscript result | Lean proof and scope |
| --- | --- |
| **Theorem A, equation (2.3)** | `GMCTilings.map_twoSidedWienerLaw_maPath` identifies the law of the radial process with the moving average of a two-sided Brownian motion on continuous path space for every $d\ge3$. `LBMHigherDim.map_sphPath` identifies this radial law with that of the centered spherical averages at any fixed center. |
| **Theorem B, first-passage limit** | With $\kappa=Q-\beta>0$, `LBMHigherDim.isFirstPassageLimit_coneRadialLaw` proves convergence in total variation on every fixed half-line $[T,\infty)$ as the level $b$ tends to infinity. The limit is the restriction of a single law on continuous two-sided paths. The declaration takes $d\ge2$, so it applies to every odd $d\ge3$. |
| **Theorem C, local limit of the field** | `LBMHigherDim.tendsto_tvDist_zoom` proves total-variation convergence on every fixed ball for the field rescaled at first passage. Lean subtracts the unit-sphere average at the deterministic zoom center $z$, as in (2.11) of this manuscript. The declaration applies for $d\ge2$ and $\beta<Q$. `GMCTilings.Cone.exists_isAlphaQuantumCone_final` supplies the cone for $d\ge3$. |

The cone results are the dimension-general lemmas inside the Bertacco–Gwynne formalization. Their hypotheses can be specialized directly to odd dimensions. The theorem letters above follow the odd-dimensional manuscript. [Bertacco–Gwynne result guide](../liouville-brownian-motion/)

## Scope still open in the formalization

A full-paper claim would also require matching proofs of the gamma-quotient and odd-dimensional spectral formulas (2.4)–(2.5), the borderline regularity and lack of a further mean-square derivative (Theorem 7.1), the obstruction to a finite-dimensional linear Gaussian realization (Proposition 7.2), and the function-valued Markov memory evolution (Theorem 7.3). The verification here is limited to the entries in the table.

The declarations were inspected in `GMCTilings` at `8171c033` and `LBMHigherDim` at `1cb4634e`. The public inspection file names the exact results and prints their axiom dependencies when run in the original private development workspace with Lean 4.34.0-rc2. [Lean inspection file](Check.lean)
