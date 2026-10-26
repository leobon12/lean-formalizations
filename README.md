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
| Jian Ding and Ewain Gwynne, *Uniqueness of the critical and supercritical Liouville quantum gravity metrics* | Theorems 1.3, 1.8 and 1.13, and equations (1.4)–(1.5): convergence of LFPP for every ξ > 0, existence and uniqueness of the strong LQG metric, and uniqueness of weak LQG metrics, under the documented predicate-form conventions | [README](results/supercritical-lqg-uniqueness/) |

## AI-generated research companions

| Paper | Accompanying Lean scope | Read the source |
| --- | --- | --- |
| Small-parameter LQG dimension | Theorem 1.1 and Proposition 1.2, with explicit LFPP literature inputs; GFF existence witness | [README](results/small-gamma-dimension/) |
| Mesh-only convergence and sharper rates on orthogonal tilings | Theorem 1.1 with the rate ε^(4/(d+4)) and Corollary 1.2 (random-walk consequences without alternatives I–III), with documented statement conventions | [README](results/mesh-only/) |
| Reflected random walks with spatial singularities | Harmonic coordinates and invariance principle in the earlier geometric-topology revision; see the revision correspondence | [README](results/reflected-gms/) |
| Gaussian fluctuations of small-γ LQG distance | Theorem 1.1 in full (all of (1.7)–(1.9), the law, q<0, unique median), unconditional — including the note's Lemma 2.1 | [README](results/gaussian-lqg-distance/) |
| A small-parameter limit for higher-dimensional LFPP | Theorem 1.1 in every dimension d ≥ 2, with no assumptions: the existence of the exponent (Ding–Gwynne–Zhuang's Proposition 1.1, with a percolation-duality gap filled) and κ_d > 0 are proved; (1.8); and d = 2 corollaries giving unconditional versions of the small-parameter LQG-dimension theorem | [README](results/higher-dim-lfpp/) |
| Small-parameter LQG geodesics: deviation and functional tightness | Theorems 1.1 and 1.2 in full, with no assumptions: the two-thirds deviation scale of the γ-LQG geodesic from 0 to 1 ((1.4)–(1.9)) and tightness of the rescaled path in C([0,1], ℝ²) with (1.11); the conformal covariance of the LQG metric that the paper cites from Gwynne–Miller is proved for maps conformal near the closure of a bounded domain | [README](results/small-parameter-lqg-geodesics/) |
| Higher-dimensional exponential metrics: axiomatic existence and uniqueness | Theorems 1.2 and 1.4 in every dimension d ≥ 3, with no assumptions: existence and uniqueness up to a deterministic constant of the exponential metric of the whole-space log-correlated field (at Q = Q(ξ)), convergence of normalized LFPP for nonnegative white-noise kernels, and uniqueness in the auxiliary weak class; the weak-metric inputs of Contreras Hip–Zhuang and the tightness theorem of Ding–Gwynne–Zhuang in dimension d are proved | [README](results/higher-dimensional-lqg-metric/) |
| Almost sure continuity of the higher-dimensional LQG metric | Theorem 1.1 in every dimension d ≥ 3, with no assumptions: the γ-LQG metrics normalized by median one, with the Euclidean metric at γ = 0, have versions on the same field that are almost surely continuous in γ ∈ [0, √(2d)) for locally uniform convergence, and on the same event every member is a continuous length metric inducing the Euclidean topology; the characterization of the metric that the paper takes as input is the higher-dimensional exponential metrics release, and the estimates of Ding–Gwynne–Zhuang uniformly in the parameter, the γ ↔ ξ parametrization and the paper's Lemma 5.1 are proved | [README](results/higher-dimensional-lqg-continuity/) |
| Conformal covariance of the supercritical Liouville quantum gravity metric | Theorem 1.1 for connected Greenian domains and globally realized fields, with no further assumption, and for every ξ > 0; Gwynne–Miller's Axiom IV form for countably many field laws | [README](results/supercritical-conformal-covariance/) |
| Almost sure convergence of higher-dimensional LFPP: an upgrade from convergence in probability | Theorem 1.2 in every dimension d ≥ 3 under the paper's Assumption 1.1, for every admissible seed (sign-changing seeds included): almost surely, the median-normalized convolution LFPP converges to the limiting metric uniformly on compact sets along all ε → 0; for nonnegative seeds with no assumptions (Assumption 1.1 is proved by the higher-dimensional exponential metrics release), the limit being every median-one strong metric; and the non-vacuity of the hypotheses | [README](results/almost-sure-higher-dimensional-lfpp/) |
| Almost sure convergence of supercritical Liouville first passage percolation | Theorem 1.1 with no assumptions, for heat-kernel versions that are almost surely jointly continuous in the cutoff and the point (such versions exist and are almost surely unique, both proved), and for every ξ > 0 | [README](results/almost-sure-supercritical-lfpp/) |

## Verify the proofs

The release pins Lean to `v4.34.0-rc2` and Mathlib to `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`; the full dependency lockfile is included. Install [elan](https://github.com/leanprover/elan), Git, and Python 3, then follow [the verification instructions](VERIFICATION.md).

The [Lean certificate](Certificate.lean) checks the named proof declarations and their axiom dependencies. The allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. This is a reproducible check of the formal statements; the result READMEs explain how those statements correspond to the papers.

## Release contents

This is a selected source snapshot from a private development repository. It includes the released proof entrypoints and their transitive source dependencies. Development history, worker conversations, scratch files, build caches, and unrelated projects are excluded. The selected small-parameter LQG-dimension theorem, its explicit input assumptions, and its GFF-existence witness are also documented above. Only the named result closures are included; unrelated development files are excluded.

Some shared dependency modules contain auxiliary results or statement definitions. The publication claims are exactly the named proof declarations in the table's READMEs; a definition of a proposition alone is not a proof.

The original mathematical results are credited to the paper authors above. Existing source-file attribution is retained.
