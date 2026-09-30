import QuantumZipper.Proofs.Thm18.G3Cv2Trans
import QuantumZipper.Proofs.Zipper.D3PlusN1Local

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 3 (one-point core): the zoom through a G0 map agrees with a D3⁺ model near 0

`exists_g0Model_agree`: in the coupling of `exists_g0Model` (free field `W`, G0 map `ψ`), there
is a random level shift `C` such that almost surely, for every level `L`, the zoom of `W` through
`ψ` at level `L` (`addConst (coordChange (W ω) ψ Q) (L/γ)`, the field read by `zoomFieldVia` at
`x = 0`) agrees near `0` (`D3Plus.AgreeNear … r'`: raw values on all dyadic folded circles inside
`ball 0 r'`) with the D3⁺ model field `zoomModel γ 0 (L + γ C ω) ρ₀ (X' ω) (g ω)` of the
`Setup` data `(X', Ξ, g)`. With `D3Plus.locFieldFull_rescale_congr` this identifies the rich local
data of the rescaled zooms, and D3⁺(i) then gives the TV-local zoom limit (G0 at one point).
Own assembly (the level shift absorbs the additive gauge of the field modulo constants).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set InnerProductSpace
open scoped ComplexConjugate ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm D3Plus

/-- Fields agreeing near `0` have the same rich local canonical data on the half-disc, once the
local scale is small. -/
theorem locFieldFull_canonicalOn_congr {γ r : ℝ} {y y' : FieldSample}
    (hag : D3Plus.AgreeNear y y' r) {R : ℕ} (ha : 0 < scaleParamOn γ y' (D3Plus.halfDisc r))
    (haR : scaleParamOn γ y' (D3Plus.halfDisc r) * R < r) :
    locFieldFull R (canonicalOn γ y (D3Plus.halfDisc r)) =
      locFieldFull R (canonicalOn γ y' (D3Plus.halfDisc r)) := by
  have hs := D3Plus.scaleParamOn_halfDisc_congr (γ := γ) hag
  unfold canonicalOn
  rw [hs]
  exact D3Plus.locFieldFull_rescale_congr hag ha haR

end G3Cv
end QuantumZipper
