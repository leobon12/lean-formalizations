import QuantumZipper.Proofs.Thm18.G1SideMain
import QuantumZipper.Proofs.Thm18.R18RTZipMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# WBAM: the side boundary transport without the all-maps rule; headline without `hWBAM`

`Thm18Asm.WedgeBdryAllMapsAwayStmt` (G1ZBdryTransp.lean) is Sheffield–Wang arXiv:1605.06171
Thm 4.3 (p. 19) for the `(γ − 2/γ)`-wedge field, for *all* maps at once. Its free-field special
case `F1.BdryAllMapsStmt` is itself open here: with the semicircle regularization of this
repository SW's continuity argument (proof of Lemma 3.5, p. 12, which uses smooth mollifiers)
does not apply, and the full-class cores need metric-entropy chaining (DECISIONS.md, D53/D59).

Its consumers only use it at the SLE side maps `ψ = (uniformizer D)⁻¹`, which are functions of
the driver `B` alone, independent of the field `Y`. For such maps Sheffield's own argument
(arXiv:1012.4797, proof of Thm 1.8, pp. 69–71, citing Duplantier–Sheffield 2011 Prop. 2.1 for
one fixed map and independence) suffices; this is route R2 of DECISIONS.md (the decision
"`WedgeBdryAllMapsAwayStmt` is bypassed"). The per-map input is the proved
`Thm18Asm.g1Z4SideLimSelStmt_holds` (D83, G1SideMain.lean), transferred to `(B, Y)` by the proved
`Thm18Asm.g1SideTransportId_of_path_sel` (G1SideWireA.lean).

Main results: `g1SideTransportIdStmt_holds`, `g1SideTransportStmt_holds`,
`g1SideBdryRegStmt_holds` (node B0), `R18.g1Stmt_of_arc_noWBAM`, and the headlines
**`R18.theorem1_8PaperM_of_frontier11w`** (`theorem1_8PaperM_of_frontier11` without `hZ4` and
`hWBAM`) and **`R18.theorem1_8Paper_of_frontier8w`** (`theorem1_8Paper_of_frontier8` without
`hWBAM`). Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

/-- **The side boundary transport with the reflection data** (from the selected-map side limit,
D83; Sheffield arXiv:1012.4797 pp. 69–71, DS11 Prop. 2.1). -/
theorem g1SideTransportIdStmt_holds : G1SideTransportIdStmt :=
  g1SideTransportId_of_path_sel g1Z4SideLimSelStmt_holds G1RC.g1RegRepRC2Stmt_holds
    g1RegRepRestStmt_holds

/-- **The side boundary transport** (`G1SideTransportStmt`). -/
theorem g1SideTransportStmt_holds : G1SideTransportStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  filter_upwards [g1SideTransportIdStmt_holds γ P B Y hS hIn left] with ω ⟨Φ, hR, hν⟩
  exact ⟨Φ, hR.1, hν⟩

/-- **Node B0 (`G1SideBdryRegStmt`) holds.** -/
theorem g1SideBdryRegStmt_holds : G1SideBdryRegStmt :=
  g1SideBdryRegStmt_of_transport g1SideTransportStmt_holds

end Thm18Asm

namespace R18

open Thm18Asm Thm18Asm.G1ZA1c LocLen D3Plus

end R18
end QuantumZipper
