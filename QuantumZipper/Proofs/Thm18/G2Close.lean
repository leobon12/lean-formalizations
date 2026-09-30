import QuantumZipper.Proofs.Thm18.G2ZoomLoc
import QuantumZipper.Proofs.Thm18.G2DisintXG
import QuantumZipper.Proofs.Thm18.G2DisintRG
import QuantumZipper.Proofs.Zipper.HeadlineWire2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 of Theorem 1.8, closed

Wiring only: the zoom-locality node `G2ZoomLocStmt` is proved (`g2ZoomLocStmt_holds`), hence the
two disintegration nodes (`g2RootXDisintStmt_of_zoom`, `g2RootRDisintStmt_of_zoom`), hence
`G2FixMixStmt` through `g2FixMixStmt_of_disint` (HeadlineWire2).
-/

namespace QuantumZipper
namespace Thm18Asm

theorem g2RootXDisintStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2RootXDisintStmt γ :=
  g2RootXDisintStmt_of_zoom hγ hγ2 (g2ZoomLocStmt_holds hγ hγ2)

theorem g2RootRDisintStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2RootRDisintStmt γ :=
  g2RootRDisintStmt_of_zoom hγ hγ2 (g2ZoomLocStmt_holds hγ hγ2)

theorem g2FixMixStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G2FixMixStmt γ :=
  g2FixMixStmt_of_disint hγ hγ2 (g2RootXDisintStmt_holds hγ hγ2) (g2RootRDisintStmt_holds hγ hγ2)

end Thm18Asm
end QuantumZipper
