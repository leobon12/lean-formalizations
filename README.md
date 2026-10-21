# Lean formalizations

Selected Lean 4 formalizations developed under the direction of Leonardo Bonanno, with AI assistance.

Each result below has a short guide to its mathematical scope, the exact Lean statement and proof, and the differences from the source paper. The source files needed by these proofs are included so that the checks can be reproduced.

| Paper | Released result | Read the formalization |
| --- | --- | --- |
| Ahmed Bou-Rabee and Ewain Gwynne, *Random walk on sphere packings and Delaunay triangulations in arbitrary dimension* | Theorems A and B(a), with the documented ambient-domain correction | [README](results/bou-rabee-gwynne/) |
| Ewain Gwynne and Jinwoo Sung, *Random walk reflected off of infinity, with applications to uniform spanning forests and supercritical Liouville quantum gravity* | Theorem 1.6 with right continuity at infinity included | [README](results/gwynne-sung/) |
| Ewain Gwynne, Jason Miller, and Scott Sheffield, *An invariance principle for ergodic scale-free random environments* | Theorem 1.16 in the documented interpolated-path formulation | [README](results/gwynne-miller-sheffield/) |
| Scott Sheffield, *Conformal weldings of random surfaces: SLE and the quantum gravity zipper* | The eight Section 1 results and three companions, with documented statement conventions | [README](results/quantum-zipper/) |
| Ewain Gwynne and Jason Miller, *Existence and uniqueness of the Liouville quantum gravity metric for γ ∈ (0,2)* | Theorems 1.1 and 1.2, with a normalized-GFF existence witness and documented statement conventions | [README](results/lqg-metric/) |

## AI-generated research companions

| Paper | Accompanying Lean scope | Read the source |
| --- | --- | --- |
| Small-parameter LQG dimension | Theorem 1.1 and Proposition 1.2, with explicit LFPP literature inputs; GFF existence witness | [README](results/small-gamma-dimension/) |
| Mesh-only convergence and sharper rates on orthogonal tilings | Theorem 1.1 with the rate ε^(4/(d+4)) and Corollary 1.2 (random-walk consequences without alternatives I–III), with documented statement conventions | [README](results/mesh-only/) |
| Reflected random walks with spatial singularities | Harmonic coordinates and invariance principle in the earlier geometric-topology revision; see the revision correspondence | [README](results/reflected-gms/) |
| Gaussian fluctuations of small-γ LQG distance | Theorem 1.1 in full (all of (1.7)–(1.9), the law, q<0, unique median), unconditional — including the note's Lemma 2.1 | [README](results/gaussian-lqg-distance/) |
| A small-parameter limit for higher-dimensional LFPP | Theorem 1.1 in every dimension d ≥ 2, with no assumptions: the existence of the exponent (Ding–Gwynne–Zhuang's Proposition 1.1, with a percolation-duality gap filled) and κ_d > 0 are proved; (1.8); and d = 2 corollaries giving unconditional versions of the small-parameter LQG-dimension theorem | [README](results/higher-dim-lfpp/) |
| Small-parameter LQG geodesics: deviation and functional tightness | Theorems 1.1 and 1.2 in full, with no assumptions: the two-thirds deviation scale of the γ-LQG geodesic from 0 to 1 ((1.4)–(1.9)) and tightness of the rescaled path in C([0,1], ℝ²) with (1.11); the conformal covariance of the LQG metric that the paper cites from Gwynne–Miller is proved for maps conformal near the closure of a bounded domain | [README](results/small-parameter-lqg-geodesics/) |

## Verify the proofs

The release pins Lean to `v4.34.0-rc2` and Mathlib to `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`; the full dependency lockfile is included. Install [elan](https://github.com/leanprover/elan), Git, and Python 3, then follow [the verification instructions](VERIFICATION.md).

The [Lean certificate](Certificate.lean) checks the named proof declarations and their axiom dependencies. The allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. This is a reproducible check of the formal statements; the result READMEs explain how those statements correspond to the papers.

## Release contents

This is a selected source snapshot from a private development repository. It includes the released proof entrypoints and their transitive source dependencies. Development history, worker conversations, scratch files, build caches, and unrelated projects are excluded. The selected small-parameter LQG-dimension theorem, its explicit input assumptions, and its GFF-existence witness are also documented above. Only the named result closures are included; unrelated development files are excluded.

Some shared dependency modules contain auxiliary results or statement definitions. The publication claims are exactly the named proof declarations in the table's READMEs; a definition of a proposition alone is not a proof.

The original mathematical results are credited to the paper authors above. Existing source-file attribution is retained.
