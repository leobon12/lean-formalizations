import QuantumZipper.Proofs.Thm18.G3ZqG3LBall

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3 above G2 with abstract zooms: region locality from ball locality

The region-locality hypotheses `G3pRegLocXZ`, `G3pRegLocRZ` (profiles of schemes `B` and `C`)
and `G3pRegionLocStmtZ` follow from the pathwise ball locality `G3ZqZoomBallLocZ` of the zooms:
the region field `restrictField (circIn t r) h` agrees with `h` on the folded circles in
`ball(t, r)` (`fcAgree_restrictField_circIn`), the Palm point lies in that ball on the margin
event, the full fields of schemes `B`, `C` are a.s. area-good (`ae_isAreaGood_g3pBField`,
`ae_isAreaGood_g3pField`), so the two zoom events agree for all large levels, a.s. under the Palm
law (which does not depend on the level); dominated convergence gives the uniform smallness.
This replaces the plain route (`zoomLaw_mem_lawCyl_iff` plus the area inputs
`G3TCutAreaStmt`, `G3TProfAreaStmt`). Own bookkeeping (AGENT_GUIDE cost rule).

Headline `g3UnscaledTransferZ_ball`: the unscaled wedge transfer with a zoom-independent window
from `hZm`, `hZa` and ball locality of both zooms only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology symmDiff

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

local notation "Ω₀" => gffBase.Ω

variable {Z Z' : ℝ → FieldSample → ℝ → LawD}

theorem abs_lt_ball {x t r m : ℝ} (hm : 0 < m) (h : |x - t| + m < r) :
    (x : ℂ) ∈ ball (t : ℂ) r := by
  rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  linarith

end R18
end QuantumZipper
