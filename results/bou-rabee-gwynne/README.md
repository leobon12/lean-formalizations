# Random walk on sphere packings and Delaunay triangulations

Lean formalization of **Theorem A and Theorem B(a)** from Ahmed Bou-Rabee and Ewain Gwynne, [*Random walk on sphere packings and Delaunay triangulations in arbitrary dimension*, arXiv:2405.11673v2](https://arxiv.org/abs/2405.11673v2).

**Scope:** the statements include the explicit ambient-domain condition `closure U ⊆ interior D`. Theorem B(b) and the applications and constructions in Sections 5–6 are outside this release's claims.

## Results and proof entrypoints

| Result | Statement | Proof |
| --- | --- | --- |
| A: uniform convergence of stopped conductance-weighted random walks to stopped standard Brownian motion, modulo time parametrization | [`TheoremAStatement`](../../BouRabeeGwynne/TheoremAStatement.lean) | [`theoremA_proved`](../../BouRabeeGwynne/TheoremAProved.lean) |
| B(a): eventual well-posedness and uniform convergence for the discrete Dirichlet problem with data harmonic near the closure of the domain | [`TheoremBPartAStatement`](../../BouRabeeGwynne/TheoremBStatement.lean) | [`theoremB_part_a`](../../BouRabeeGwynne/Section3TheoremBPartA.lean) |

The graphs arise from orthogonal tilings by convex polytopes. Edge conductances are the contact's codimension-one volume divided by the distance between the marked vertices. The formalization retains the global approximation hypothesis and the sequence-level regularity alternatives I, II, or III.

Theorem A uses a Lipschitz domain. It compares the actual stopped-walk and Brownian laws using Prokhorov distance for the Fréchet metric on curves modulo time parametrization, uniformly over starting points in the domain. Theorem B(a) does not add a Lipschitz assumption: its boundary data come from one function harmonic on a fixed open neighborhood of the domain's closure.

## Correspondence with the paper

The ambient collar `closure U ⊆ interior D` is an explicit correction to the paper's literal ambient-set hypotheses. The nearest-vertex convention, immediate exit, external graph-boundary values, and the full discrete Laplacian are built into the linked statements and their definitions.

The source also contains a definition of the full Theorem B statement. Only the proof of **B(a)** is claimed here. Likewise, helper implications with assumed error estimates are not the main proof: the entrypoints in the table prove the actual geometric and probabilistic statements.

## Check this result

See [verification instructions](../../VERIFICATION.md) and the [certificate](../../Certificate.lean). The certificate checks

```lean
BouRabeeGwynne.theoremA_proved : BouRabeeGwynne.TheoremAStatement
BouRabeeGwynne.theoremB_part_a : BouRabeeGwynne.TheoremBPartAStatement
```

The Lean and Mathlib versions are pinned in the repository. The release includes all local proof dependencies; no access to the private development repository is needed.

[All released formalizations](../../README.md)
