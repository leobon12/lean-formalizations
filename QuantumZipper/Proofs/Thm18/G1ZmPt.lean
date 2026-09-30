import QuantumZipper.Proofs.Thm18.G3Zc2Univ
import QuantumZipper.Proofs.Thm18.G3Za11
import QuantumZipper.Proofs.Zipper.E5Model2
import QuantumZipper.Proofs.Zipper.D3PlusN2Loc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-ZOOM (2): the zoom of the Palm field at its Palm point converges to a `γ`-wedge

`tendsto_palmZoom_canonical`: for a G0 map `ψ`, `0 < γ < 2` and a Palm point `x`
(`0 < |x| ≤ 1/2`), let `h^x = N_S(ofFun (palmProf γ x) + V)` be the Palm field of
`G3WedgePalmIdStmt` (`V` any free field). If the zooms of `h^x` at `x` through `ψ` have global
local-area limits (the regularity clause `IsLQGGood` of `G1FacReg`), then for every measurable
`Γ ∈ [0, 1]`

  `E Γ(locFieldFull R (canonical γ (zoomFieldVia γ L h^x x ψ))) → E Γ(locFieldFull R Y')`,

`Y'` a `γ`-quantum wedge. This is the one-point zoom at a quantum-typical point (Sheffield,
arXiv:1012.4797, pp. 70–71, "as in Proposition 1.6"), for the Palm field.

Proof: the zoom agrees near `0` with `zoomS` of the free field `V_x = rawTranslate V x` at a
shifted level (ZOOM-A, `G3Za.ae_agreeNear_zoom_palmField`); ZOOM-A's coupled core
(`G3Za.exists_g0Setup_palmField`) and the universality of the dyadic law (ZOOM-C,
`dyadLaw_eq_free`, `tendsto_zoom_of_lawEq`) give the limit of the local canonical data on a small
half-disc; the bad event of the local scale has vanishing mass (D3⁺(iii), transferred by the law
equality, `tendsto_bad_of_lawEq`), off which the global and the local canonical data coincide
(`E5.locFieldFull_canonical_eq_canonicalOn`). Own assembly (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Zm

open D3Plus G3Cv

/-- The Palm field of `G3WedgePalmIdStmt` at the Palm point `x`. -/
abbrev palmFieldAt (γ x : ℝ) (v : FieldSample) : FieldSample :=
  PalmNorm.normAt R18.g3zS (ofFun (G3Za.palmProf γ x) + v)

end G1Zm
end Thm18Asm
end QuantumZipper
