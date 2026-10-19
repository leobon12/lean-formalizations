-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPP.Frozen.Kappa
import LQGDimension.Statement.Defs
import HigherDimLFPP.Var.Theorem11

/-!
# Frozen theorem: `kappa_two_eq`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1 and the planar input [5] (the 2D paper, `LQGDimension`).  Ruling H4: the planar
constant of the 2D paper is `a*/log 16`, and `κ₂` equals it exactly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- `κ₂ = a*/log 16`, where `a* = LQGDimension.aStar` is the constant of the 2D paper. -/
theorem kappa_two_eq : kappa 2 = LQGDimension.aStar / Real.log 16 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPP.kappa_two_eq_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPP
-- FROZEN_ANCHOR_SUFFIX_END
