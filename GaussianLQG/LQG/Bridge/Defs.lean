import LQGMetric.Statement.Thm12
import GaussianLQG.Frozen.IsCanonicalLQGMetric

/-!
# The canonical γ-LQG metric (draft predicate)

Blueprint Definition `def:metric`: for `γ ∈ (0,2)`, `D^γ_h` is the γ-LQG metric of
Gwynne–Miller (arXiv:1905.00383v3), Theorems 1.1–1.2, which is the limit in probability, for the
local uniform topology, of `𝔞_ε⁻¹ D^ε_h` as `ε → 0`.

`IsCanonicalLQGMetric γ D` is the existence clause of `LQGMetric.Theorem12`: `D` is a strong
γ-LQG metric (`LQGMetric.IsStrongLQGMetric`, Axioms I–IV of GM) and, for every whole-plane GFF
plus a bounded continuous function `h`, `𝔞_ε⁻¹ D^ε_h → D_h` in probability for the local uniform
topology as `ε → 0⁺`.

The definition itself is frozen in `GaussianLQG/Frozen/IsCanonicalLQGMetric.lean` (manifest
`GaussianLQG/Frozen/frozen-anchors.json`); this file re-exports it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter Topology

namespace GaussianLQG

-- `IsCanonicalLQGMetric` (blueprint Definition `def:metric`) is the frozen definition
-- `GaussianLQG/Frozen/IsCanonicalLQGMetric.lean`.

end GaussianLQG
