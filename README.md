# Lean formalizations

Selected Lean 4 formalizations developed under the direction of Leonardo Bonanno, with AI assistance.

Each result below has a short guide to its mathematical scope, the exact Lean statement and proof, and the differences from the source paper. The source files needed by these proofs are included so that the checks can be reproduced.

| Paper | Released result | Read the formalization |
| --- | --- | --- |
| Ahmed Bou-Rabee and Ewain Gwynne, *Random walk on sphere packings and Delaunay triangulations in arbitrary dimension* | Theorems A and B(a), with the documented ambient-domain correction | [README](results/bou-rabee-gwynne/) |
| Ewain Gwynne and Jinwoo Sung, *Random walk reflected off of infinity, with applications to uniform spanning forests and supercritical Liouville quantum gravity* | Theorem 1.6 with right continuity at infinity included | [README](results/gwynne-sung/) |
| Ewain Gwynne, Jason Miller, and Scott Sheffield, *An invariance principle for ergodic scale-free random environments* | Theorem 1.16 in the documented interpolated-path formulation | [README](results/gwynne-miller-sheffield/) |

## Verify the proofs

The release pins Lean to `v4.34.0-rc2` and Mathlib to `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`; the full dependency lockfile is included. Install [elan](https://github.com/leanprover/elan), Git, and Python 3, then follow [the verification instructions](VERIFICATION.md).

The [Lean certificate](Certificate.lean) checks the named proof declarations and their axiom dependencies. The allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. This is a reproducible check of the formal statements; the result READMEs explain how those statements correspond to the papers.

## Release contents

This is a selected source snapshot from a private development repository. It includes the released proof entrypoints and their transitive source dependencies. Development history, worker conversations, scratch files, build caches, and unrelated projects are excluded. Quantum Zipper is not part of this release.

Some shared dependency modules contain auxiliary results or statement definitions. The publication claims are exactly the named proof declarations in the table's READMEs; a definition of a proposition alone is not a proof.

The original mathematical results are credited to the paper authors above. Existing source-file attribution is retained.
