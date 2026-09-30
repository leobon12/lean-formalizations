import QuantumZipper.Proofs.Thm18.G1Z3Fixed
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1RegRepRed
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp
import QuantumZipper.Proofs.Thm18.G1ProfileRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE (D83): the side-limit node at the selected side maps, for almost every path

`G1Z4SideLimPathStmt` (G1Z4Defs.lean) asks for the side boundary limit along all radii of the
canonical wedge representative pulled back by an ARBITRARY fixed inverse normalized uniformizer of
a side domain of an ARBITRARY simple chord. Its only consumer (`g1z5_ae_mem_repGood`,
G1Z5Main.lean, through which all uses pass) applies it at the selected side maps `Ψ left a` of
almost every SLE path `a`. The proof needs RC3 of the pulled-back canonical field at the
circles near the side half-line, which the repository has for the selected SLE side maps
(`Thm18Asm.G1Rest.ae_rc3_rep`, from the Rohde–Schramm boundary regularity of SLE), but not for an
arbitrary chord. Decision D83: the node is stated at the selected maps for almost every path
(`G1Z4SideLimSelStmt`); it is implied by `G1Z4SideLimPathStmt` (`g1Z4SideLimSelStmt_of_path`).
Mathematically this is the same step of the paper (Sheffield, arXiv:1012.4797, §1.6 and proof of
Theorem 1.8, pp. 69–71; Duplantier–Sheffield 2011 Prop. 2.1 at a map independent of the field).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **Node S2 at the selected side maps, a.e. path** (D83). -/
def G1Z4SideLimSelStmt : Prop :=
  G1RepSetting fun γ _ _ P B _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ᵐ a ∂(P.map (pathOf B)), ∀ left : Bool, ∀ Φ : ℝ ≃o ℝ, SideReflGood left (Ψ left a) Φ →
      ∀ᵐ ω' ∂P', G1Z2SideBdryLim γ left (coordChange (wedgeRep γ X A ω') (Ψ left a) (Qc γ))
        (((qBoundaryMeasure γ (wedgeRep γ X A ω')).restrict (g1SideHalf left)).map Φ.symm)

end Thm18Asm
end QuantumZipper
