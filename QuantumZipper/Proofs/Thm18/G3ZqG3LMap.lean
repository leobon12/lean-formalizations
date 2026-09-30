import QuantumZipper.Proofs.Thm18.G3ZqG3LReg
import QuantumZipper.Proofs.Thm18.G3ZqMapZ
import QuantumZipper.Proofs.Thm18.G3ZqNodes
import QuantumZipper.Proofs.Thm18.G3ZpLoc
import QuantumZipper.Proofs.Thm18.G3ZpExt
import QuantumZipper.Proofs.Thm18.G1Z2ReflChord
import QuantumZipper.Proofs.Thm18.G1ProfileConv

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Ball locality with an abstract goodness condition; the map zoom of a good path

`G3ZqZoomBallLocGZ Z Gd`: ball locality of the zoom `Z` at level `→ ∞` under a goodness condition
`Gd y' x` on the second field at the point (the plain condition `g3PlainGd γ` gives
`G3ZqZoomBallLocZ`, `g3ZqZoomBallLocZ_iff`). For the zoom `g3zMapZ γ Ψ side a` through the local
maps of a good path `a`, ball locality holds with the goodness condition `g3zMapGd` — on the side
half-line: the pulled-back zoomed field `reconstruct (g3coordsM γ 0 Ψ side (y', a, 1, x))` is good
with positive area on every half-ball; off it: the plain condition
(`g3zMapZ_ballLocG`, from `G3Zp.g3zoomLawM_eventually_iff_ball` and `G3Zp.g3mapP_ext`, the side
reflection `G1Z2.sideReflChordStmt_holds` and `G1RC.psiGood_of_sel`).

So `G3ZqZoomBallLocZ (g3zMapZ …) γ` itself (with the plain condition on `y'`) is **not** what the
map zoom satisfies; the region-locality derivations of `G3ZqG3LReg.lean` go through verbatim with
`g3zMapGd` once the scheme fields satisfy it a.s. at every side point (the area goodness of the
pulled-back field). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G Factorization G3Z2b2 G3Zp G3Zq

/-- **Ball locality under a goodness condition `Gd`.** -/
def G3ZqZoomBallLocGZ (Z : ℝ → FieldSample → ℝ → LawD) (Gd : FieldSample → ℝ → Prop) : Prop :=
  ∀ s ∈ lawCyl, ∀ (y y' : FieldSample) (x : ℝ) (W : Set ℂ), IsOpen W → FcAgree W y y' →
    (x : ℂ) ∈ W → Gd y' x → ∀ᶠ C in (atTop : Filter ℝ), (Z C y x ∈ s ↔ Z C y' x ∈ s)

/-- The plain goodness condition: the translated field is good with positive area. -/
def g3PlainGd (γ : ℝ) (y : FieldSample) (x : ℝ) : Prop :=
  IsLQGGood γ (translate y (x : ℂ)) ∧ ∀ q : ℝ, 0 < q → 0 < areaProxy γ (translate y (x : ℂ)) q

end R18
end QuantumZipper
