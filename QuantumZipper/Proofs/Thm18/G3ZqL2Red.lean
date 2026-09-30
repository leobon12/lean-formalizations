import QuantumZipper.Proofs.Thm18.G3ZqL1Loc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-LOC (2): `G3ZqZoomLocStmt` from the area regularity of the pulled-back free field

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, p. 66 (the zoom at the root does not see a bump
away from it). `G3Zq.G3ZqZoomLocStmt` asks, for a fixed good path `a` and the free field, that at
every point `x` the zoom `g3zMapZ` (through the local map on the side half-line, plain elsewhere)
does not see a bump vanishing near `x`, for all large levels.

* Off the side half-line this is the plain zoom locality `g2ZoomLocStmt_holds`.
* On the side half-line it is the area-only deterministic core `G3ZqL.g3zoomLawM_bump_iffA`, with
  the continuous boundary extension of the local map from the Schwarz reflection of the side map
  (`G3Zp.g3mapP_ext`, `G1Z2.sideReflChordStmt_holds`), provided the pulled-back zoomed field at
  level `0` is area-regular with positive area on every half-ball about `0`, a.s. at every side
  point simultaneously: this is the node `G3ZqLAreaStmt`.

Headline: `g3ZqZoomLocStmt_of_area`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3ZqL

open G3Z2b2 G3Zp G3Zq Factorization

/-- The pulled-back zoomed free field at level `0` through the local map of the path `a` at the
side point `x`. -/
def g3zqPull (γ : ℝ) (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ) (side : Bool) (a : ℝ≥0 → ℝ)
    (y : FieldSample) (x : ℝ) : FieldSample :=
  reconstruct (g3coordsM γ 0 Ψ side (y, a, 1, x))

end G3ZqL
end Thm18Asm
end QuantumZipper
