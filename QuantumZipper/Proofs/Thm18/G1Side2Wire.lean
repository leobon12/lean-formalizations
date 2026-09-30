import QuantumZipper.Proofs.Thm18.G1Side2Bdry
import QuantumZipper.Proofs.Thm18.G1ZA2STMain
import QuantumZipper.Proofs.Thm18.G1ZB2RNode
import QuantumZipper.Proofs.Thm18.R18G3Wire
import QuantumZipper.Proofs.Thm18.R18G3Defs
import QuantumZipper.Proofs.Thm18.R18G1ArcWire
import QuantumZipper.Proofs.Thm18.R18G1ArcReg
import QuantumZipper.Proofs.Thm18.R18G1ArcLenDet
import QuantumZipper.Proofs.Thm18.G1ZA1cMain
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Thm18.G1FM2Final
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1Z2MeasRep
import QuantumZipper.Proofs.Thm18.G1Z5Id
import QuantumZipper.Proofs.Thm18.G1ZB2CGeom
import QuantumZipper.Proofs.Thm18.G1ZZ1Main
import QuantumZipper.Proofs.Thm18.G1ZoomNodes
import QuantumZipper.Proofs.Thm18.G1ZoomPalmCov
import QuantumZipper.Proofs.Thm18.JordanChordA1a
import QuantumZipper.Proofs.Thm18.Thm18HeadlineV3
import QuantumZipper.Proofs.Thm18.R18G3PalmConst
import QuantumZipper.Proofs.Thm18.R18G3Const
import QuantumZipper.Proofs.Thm18.R18G3Z1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE2 (2): `G1Z2SideGoodStmt` from its area clause; headline version 9

The boundary clause of `G1Z2SideGoodStmt` is proved (`ae_sideBdryLim_all`, G1Side2Bdry.lean).
What remains is the area clause, stated as `G1Z2SideAreaStmt`: almost surely, for every normalized
uniformizer of the side domain, the pulled-back wedge field has an area limit on `ℍ` along all
radii, of mass `< 1` near every real point and of infinite total mass (Sheffield–Wang,
arXiv:1605.06171, Thm 1.4 and Thm 4.3 for the area measure; the infinite total mass is the
side surface having infinite quantum area, Sheffield arXiv:1012.4797 Thm 1.8: each side is a
`γ`-quantum wedge).

With `G1Z2SideGoodStmt` in hand, the G1 leaves `G1RerootFactorStmt` (`g1RerootFactorStmt_of_good`)
and `G1PalmConstStmt` (`g1PalmConstStmt_of_nodes`) are no longer hypotheses of the headline:
`R18.theorem1_8Paper_of_frontier9`. Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

/-- **Node (area clause of the side goodness).** -/
def G1Z2SideAreaStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool,
    ∀ᵐ ω ∂P, ∀ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom (sleTrace (γ ^ 2) B ω) left) φ →
      ∃ μ : Measure ℂ, HasAreaLimit γ
          (coordChange (Y ω) (invFunOn φ (sideDom (sleTrace (γ ^ 2) B ω) left)) (Qc γ)) μ ∧
        (∀ p : ℝ, ∃ a : ℝ, 0 < a ∧ μ (Metric.ball (p : ℂ) a ∩ H) < 1) ∧ μ H = ⊤

/-- **`G1Z2SideGoodStmt` from its area clause.** -/
theorem g1Z2SideGoodStmt_of_area (hA : G1Z2SideAreaStmt) : G1Z2SideGoodStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  filter_upwards [hA γ P B Y hS hIn left, ae_sideBdryLim_all γ P B Y hS hIn left]
    with ω h1 h2 φ hφ
  exact ⟨h1 φ hφ, h2 φ hφ⟩

end Thm18Asm

namespace R18

open Thm18Asm

end R18
end QuantumZipper
