import QuantumZipper.Proofs.Thm18.G3Pl2Meas
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1Pair
import QuantumZipper.Proofs.Section5.Prop17Field
import QuantumZipper.Proofs.Zipper.WedgeAddConstReDet
import QuantumZipper.Proofs.Zipper.ZipLenField
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.Wire2b

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b): from the canonical representative to the unscaled wedge field

`wedgeRep γ X A = canonical γ W = rescale W Q (scaleParam γ W)` with `W` the unscaled
(circle-average embedding) wedge field `wedgeField (lateralPart X) A Q`. By dilation invariance
of the Palm-window functional (`g3plPhi_rescale`), `E[Φ(wedgeRep)] = E[Φ(W)]` as soon as, a.s.,
`W` is good (`LogSingGood.wedgeRefGoodAS_holds`), `scaleParam γ W > 0`
(`Wire2.ae_wedge_canonical_spec`), its zooms have positive scale parameters
(`G3Pl3ZoomPosStmt`) and its smoothed pairings against dilated test measures converge
(`G3Pl3PairLimStmt`, PAIR-LIM; Duplantier–Sheffield 2011 Prop. 3.1, Sheffield–Wang
arXiv:1605.06171 Lemmas 3.4–3.5). The comparison is then stated for `W`
(`G3PlPhiUnscaledStmt`, target of part (b): coupling and locality). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- The unscaled (circle-average embedding) wedge field. -/
abbrev g3plUW (γ : ℝ) {Ω' : Type} (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (ω : Ω') :
    FieldSample :=
  wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)

end R18
end QuantumZipper
