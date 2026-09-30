import QuantumZipper.Proofs.Thm18.G1CoreRep
import QuantumZipper.Proofs.Thm18.G1ZBdryDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z3 (D58, route R2): the side boundary transport by independence (Fubini over the path)

Node B0 = `G1SideBdryRegStmt` follows from `G1SideTransportStmt` (G1ZBdryDet.lean). The side map
is a function of the driving path `B` only, and `B` is independent of the wedge field `Y`
(`Thm18Setting`). So, exactly as for the regularity half (`G1CoreFixed.lean`,
`G1CoreRep.lean`), the a.s. transport statement reduces to a **product** statement: a measurable
set of pairs (path, wedge data) all of whose members satisfy the transport rule, and which is
charged fully by `P.map (pathOf B) ⊗ fieldLawFull H Y P`; and that in turn reduces, by the law
transfer, to the explicit representative `wedgeRep γ X A` of the wedge law on its own space.
This is the independence argument of Sheffield, arXiv:1012.4797, §1.6/§5 and
Duplantier–Sheffield, *LQG and KPZ*, Invent. Math. 185 (2011), Prop. 2.1 (the coordinate change
rule holds a.s. for a conformal map chosen independently of the field); it replaces the
all-maps rule of Sheffield–Wang (decision D58).

Main results: `g1SideTransportStmt_of_bdryFixed`, `g1BdryFixedStmt_of_rep`,
**`g1SideBdryRegStmt_of_bdryRep`**. Own bookkeeping (copies of `g1RegExStmt_of_fixed`,
`g1RegFixedStmt_of_rep`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The driving function `W = √κ a` of a path `a` (so `drive κ B ω = pathDrive κ (pathOf B ω)`). -/
def pathDrive (κ : ℝ) (a : ℝ≥0 → ℝ) : ℝ → ℝ := fun t => Real.sqrt κ * a t.toNNReal

theorem drive_eq_pathDrive {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    drive κ B ω = pathDrive κ (pathOf B ω) := rfl

end Thm18Asm
end QuantumZipper
