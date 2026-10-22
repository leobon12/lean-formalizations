import HigherDimLQGMetric.Frozen.DistRd
import HigherDimLQGMetric.Frozen.BumpTest
import HigherDimLQGMetric.Frozen.UnitSphereProb

/-!
# Frozen definition: `sphereAvg`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 57–59 (`h_r(z)`, the spherical average; `s_r(z) = r^{ξQ} e^{ξ h_r(z)}`), [1] §1.2 ("the spherical
average process ... admits a continuous modification"): `h_r(z) := lim_n ∫ ⟨h, ψ_{n, z + r u}⟩ dσ(u)`
(mollify, then average over the sphere `∂B_r(z)`). `limUnder` (junk value: an unspecified constant when
the limit does not exist); the characterization theorem `sphereAvg_spec` (frozen) states that for every
LGF plus a continuous function the limit exists almost surely, at every fixed `(r, z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h_r(z)`: the limit of the sphere averages of the mollified field `x ↦ ⟨h, ψ_{n,x}⟩`. -/
def sphereAvg {d : ℕ} (h : DistRd d) (r : ℝ) (z : Rd d) : ℝ :=
  limUnder atTop fun n : ℕ => ∫ u, h (bumpTest n (z + r • u)) ∂(unitSphereProb d)

end HigherDimLQGMetric
