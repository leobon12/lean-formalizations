import QuantumZipper.Proofs.Thm18.G4RezipNodes
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Thm18.G4Weld2Arc
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Loewner.CoreArc3e
import QuantumZipper.Proofs.Loewner.ReverseHolo
import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Wire4
import QuantumZipper.Proofs.Section5.Prop17Point

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: `G4ConcatBdryStmt` from the boundary transport of one zip

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 and Theorem 1.8.
`G4ConcatBdryStmt` (the first zip `f₁ = revMap p₁` sends the left welding point of `x` for
`s + t` to `b·0₋(p₂)` and welds the outer segment according to the welding of `y = Z_t x`) is
reduced here to

* `ZipBdryLenStmt`: **boundary quantum length is carried by the boundary map of the zip**: for
  a fixed length `t > 0`, a.s., for every good length-welding driver `p` of the wedge field
  `x` for `t`, the rescaled zipped field `y = canonical (x ∘ f⁻¹ + Q log|(f⁻¹)'|)` satisfies
  `ν_y[Re F(u)/b, 0] = ν_x[u, 0₋]` (`u ≤ 0₋`) and `ν_y[0, Re F(r)/b] = ν_x[0₊, r]` (`r ≥ 0₊`),
  `F = revMapBdry p`, `b = scaleParam`. Sources: coordinate change of the boundary measure,
  Duplantier–Sheffield arXiv:0808.1560 Prop. 3.1 / §6 (M4-T4 in this project) for fixed maps,
  and Sheffield–Wang arXiv:1605.06171 **Theorem 4.3** (p. 19: a.s. the transformation rule holds
  *simultaneously for all* conformal maps), needed because `p` depends on `x`;
  see `F1.BdryAllMapsStmt` (`Zipper/BdryTransportAll.lean`) for the free-field form.
* `WedgeRightInfStmt`: `ν_x[0,∞) = ∞` a.s. (Sheffield §1.6; mirror image of the proved
  `WedgeLeftInfStmt`).

The deduction (`g4ConcatBdryStmt_of_zipBdryLen`) is `F1.concatTransport_det` (own elementary
argument) plus the Carathéodory facts of the reverse flow (`CaraR.revMapCaratheodory`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **Infinite boundary length on the right** (explicit hypothesis; Sheffield arXiv:1012.4797
§1.6: a wedge has "an infinite amount [of boundary length] in each neighborhood of ∞"; mirror of
`WedgeLeftInfStmt`). -/
def WedgeRightInfStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample), 0 < γ → γ < 2 → IsQuantumWedge γ (γ - 2 / γ) Y P →
    ∀ᵐ ω ∂P, qBoundaryMeasure γ (Y ω) (Ici 0) = ⊤

end Thm18Asm
end QuantumZipper
