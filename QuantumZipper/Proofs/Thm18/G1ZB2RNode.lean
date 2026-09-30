import QuantumZipper.Proofs.Thm18.G1ZB2RCrux
import QuantumZipper.Proofs.Thm18.G1ZB2RMain
import QuantumZipper.Proofs.Thm18.G1ZMeasReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-B2R (5): the canonical-data identity for the side field, and `G1PalmConstStmt`

Theorem 1.8, G1 zoom, node B2-R. Sheffield, arXiv:1012.4797, proof of Proposition 1.7, pp. 25–26.

`g1SideConstDataStmt_of : G1RegExStmt → G1Z2SideGoodStmt → G1SideConstDataStmt`: a.s. the
(epsilon-chosen) side field `Z` is `RegEq` to a dilation of the pulled-back field `x` of a
normalized uniformizer (U6, `g1z2_regEq_dilate`, exactly as in `g1SideRerootRepStmt_of`), and `x`
has the regularity package (RC2 and PAIR-LIM from `G1RegExStmt`, the LQG area measure from
`G1Z2SideGoodStmt`); then `g1zB2r_const_data` applies to `Z` and all its real translates.

`g1PalmConstStmt_of_nodes`: `G1PalmConstStmt` from A (`G1RerootStmt`), B0 (`G1SideBdryRegStmt`),
the regularity half (`G1RegExStmt`) and the LQG-measure node (`G1Z2SideGoodStmt`); B1-MEAS is
`g1SideTranslMeasStmt_of_good`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization CoordsFull

/-- **`G1SideConstDataStmt` from the regularity half and the LQG-measure node.** -/
theorem g1SideConstDataStmt_of (hR : G1RegExStmt) (hG : G1Z2SideGoodStmt) :
    G1SideConstDataStmt := by
  intro γ Ω _ P _ B Y hS hIn left C
  have hγ : 0 < γ := hS.1
  have hside : G1RegExSide γ P B Y left := by
    cases left
    · exact (hR γ P B Y hS hIn).2
    · exact (hR γ P B Y hS hIn).1
  filter_upwards [hside, hIn.2.2, hG γ P B Y hS hIn left,
    g1SideRegSampleStmt_of_regEx hR γ P B Y hS hIn left]
    with ω ⟨φ, hφ, hcore⟩ hω hgood hZreg
  have hη : IsSimpleChord (pathTrace (γ ^ 2) (pathOf B ω)) := hω.1
  have hu : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) (pathOf B ω)) left)
      (uniformizer (sideDom (pathTrace (γ ^ 2) (pathOf B ω)) left)) := by
    cases left
    · exact hω.2.2.2
    · exact hω.2.2.1
  have hD : IsOpen (sideDom (pathTrace (γ ^ 2) (pathOf B ω)) left) :=
    G1.isOpen_component hω.1 left
  obtain ⟨hψd, hψ0, hψm, -⟩ := G1.invFunOn_props hD hφ
  have hint := G1.choiceRegular_logDeriv hD hφ
  have hexact := hcore.2.1
  obtain ⟨b, hb, hbeq⟩ := g1z2_invFunOn_eq_dilate hη left hφ hu
  have hZx := g1z2_regEq_dilate (Y ω) (Qc γ) hψd hψ0 hψm hb hbeq hint hexact
  exact g1zB2r_const_data hγ C hcore.1 hcore.2.2 (hgood φ hφ).1 hZreg hb hZx

/-- **B2-R (`G1PalmConstStmt`) from A, B0, the regularity half and the LQG-measure node.** -/
theorem g1PalmConstStmt_of_nodes (hA : G1RerootStmt) (hB0 : G1SideBdryRegStmt)
    (hR : G1RegExStmt) (hG : G1Z2SideGoodStmt) : G1PalmConstStmt :=
  g1PalmConstStmt_of hA hB0 (g1SideTranslMeasStmt_of_good hR hG) (g1SideConstDataStmt_of hR hG)

end Thm18Asm
end QuantumZipper
