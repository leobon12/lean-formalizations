import QuantumZipper.Proofs.Thm18.G2PalmGood
import QuantumZipper.Proofs.Thm18.G2PalmLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 identification nodes: the three leaves of db1d7a5, proved

For `0 < γ < 2`: `G2PalmGoodStmt γ` (`g2PalmGoodStmt_holds`), `G2RootXCutLocStmt γ` and
`G2RootRCutLenLocStmt γ` (locality of the cut lengths, from goodness, `G2PalmLoc.lean`). Hence
`G2FixMixStmt γ` follows from D3⁺(i) (N2 form), the two Palm identities and the two length
smoothing nodes alone (`g2FixMixStmt_of_palmLeaves`).

Sources: Sheffield, arXiv:1012.4797, §5.4, proof of Prop. 5.5 (pp. 65–66) and of Thm. 1.8
(pp. 70–72); see `G2PalmGood.lean`, `G2PalmLoc.lean`.
-/

namespace QuantumZipper
namespace Thm18Asm

theorem g2RootXCutLocStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2RootXCutLocStmt γ :=
  g2RootXCutLocStmt_of_good (g2PalmGoodStmt_holds hγ hγ2)

theorem g2RootRCutLenLocStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    G2RootRCutLenLocStmt γ :=
  g2RootRCutLenLocStmt_of_good (g2PalmGoodStmt_holds hγ hγ2)

/-- **`G2FixMixStmt` from D3⁺(i) (N2 form), the Palm identities and the length smoothing.** -/
theorem g2FixMixStmt_of_palmLeaves {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hPX : G2RootXPalmIdStmt γ) (hSX : G2RootXLenSmoothStmt γ)
    (hPR : G2RootRPalmIdStmt γ) (hSR : G2RootRLenSmoothStmt γ) :
    G2FixMixStmt γ :=
  g2FixMixStmt_of_finalLeaves hγ hγ2 hN2 hPX hSX hPR hSR (g2PalmGoodStmt_holds hγ hγ2)
    (g2RootXCutLocStmt_holds hγ hγ2) (g2RootRCutLenLocStmt_holds hγ hγ2)

end Thm18Asm
end QuantumZipper
