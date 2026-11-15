# Third-party code in this repository

The Lean libraries `MathFin` (directory `MathFin/`) and `BrownianMotion` (directory `BrownianMotion/`) are
third-party code licensed under the Apache License, Version 2.0. They were copied into the development of the
[elementary SLE₈ continuity formalization](../results/elementary-sle8-continuity/) and of the
[Imaginary Geometry I formalization](../results/imaginary-geometry-i/) (one development project) and **modified: ported to
Lean v4.34.0-rc2 / Mathlib a4c8ef0a** (from Lean v4.35.0 / Mathlib e91b1280). This repository ships only the modules
that the released proofs import (67 `MathFin` and 47 `BrownianMotion` modules), byte-identical to the ported files.

| Directory | Lean library | Origin | Revision | License |
|---|---|---|---|---|
| `MathFin/` | `MathFin` | https://github.com/formal-applied-math/formal-mathfin | `db26174` | Apache-2.0 ([`vendor/formal-mathfin/LICENSE`](formal-mathfin/LICENSE)) |
| `BrownianMotion/` | `BrownianMotion` | https://github.com/RemyDegenne/brownian-motion | `497e5e2a60450796f75ab920e6c33addae4d644d` (the revision formal-mathfin `db26174` pins) | Apache-2.0 ([`vendor/brownian-motion/LICENSE`](brownian-motion/LICENSE)) |

Every file keeps its upstream copyright header. Every local change is marked in the file by a comment starting
`-- PORT (interacting_sle, ruling R20):` (`interacting_sle` is the development project of both formalizations, and R20
the development decision to port these libraries instead of rebuilding them). In summary:

- renamed or changed Mathlib API adapted to Mathlib a4c8ef0a (each change marked in place);
- upstream declarations whose proofs are unfinished (`sorry`), and the declarations that use them, removed (marked in
  place); no shipped module contains `sorry`;
- each file sets the upstream package options `autoImplicit false` and `relaxedAutoImplicit false`.

The upstream `LICENSE` files are kept unchanged in `vendor/formal-mathfin/` and `vendor/brownian-motion/`. The Apache
License 2.0 is also at https://www.apache.org/licenses/LICENSE-2.0.

## Jordan curve theorem port

The 14 files `InteractingSLE/Foundations/Topology/Jordan/*.lean` (and the 13 earlier released files
`MatedCRTHarmonic/Planar/Topology/Jordan/*.lean`) are a port of R. Kirov's formalization of Maehara's proof of the
Jordan curve theorem, https://github.com/rkirov/jordan_pick (Apache-2.0), commit
`b3c9b7cf7358bf81a077d78ad67e6e8247869ddd`, file `JordanPick/JordanCurve.lean`. Each file names its upstream source.
The original proofs are kept and changed only where this release's Lean and Mathlib force it; the
namespace was renamed and `private` dropped so that the upstream file could be split into modules. The Apache License
2.0 is the license in `vendor/formal-mathfin/LICENSE`, also at https://www.apache.org/licenses/LICENSE-2.0.
