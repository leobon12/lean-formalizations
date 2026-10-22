import HigherDimLFPP.Frozen.Rd
import Mathlib.Topology.ContinuousMap.Defs

/-!
# Frozen definition: `euclidDistC`

Anchor of the statement surface of the HigherDimLQGContinuity formalization (manifest
`HigherDimLQGContinuity/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, N1, N4).
Source: `source/higher-dimensional-lqg-continuity.pdf` ([C], sha256 `05368f93…2f9c2e5934`, cited by line of the
text extraction `source/higher-dimensional-lqg-continuity.txt`): Theorem 1.1, l. 36 ("set `D⁰_h(x, y) = |x − y|`").
The Euclidean distance of `ℝ^d` (`HigherDimLFPP.Rd d = EuclideanSpace ℝ (Fin d)`), as a point of
`C(ℝ^d × ℝ^d, ℝ)`, the codomain of the versions (ruling N4). Literal definition; no junk branch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)

/-- `D⁰_h(x, y) = |x − y|`: the Euclidean distance of `ℝ^d` as a continuous function on `ℝ^d × ℝ^d`. -/
def euclidDistC (d : ℕ) : C(Rd d × Rd d, ℝ) :=
  ⟨fun p => dist p.1 p.2, continuous_dist⟩

end HigherDimLQGContinuity
