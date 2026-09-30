import QuantumZipper.Proofs.Zipper.T13Hard3Defs
import QuantumZipper.Proofs.Zipper.T13MiscTransferY
import QuantumZipper.Proofs.Zipper.WedgeDecompCore
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.F1Side3
import QuantumZipper.Proofs.Zipper.WedgeFlowWDMain
import QuantumZipper.Proofs.Zipper.WedgeCocycleCore
import QuantumZipper.Proofs.Zipper.F1LenInScale
import QuantumZipper.Proofs.Zipper.F1Reg2XFlowMain
import QuantumZipper.Proofs.Zipper.XFlowClose
import QuantumZipper.Proofs.Thm18.G4CoreDefs2
import QuantumZipper.Proofs.Thm18.G4CapLen
import QuantumZipper.Proofs.Thm18.G4BSidePos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 Core B (task G4C-2): the law-free capacity field cocycle at the wedge

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 (the capacity zipper is
a flow), §5.1 (B3(d): unzipping commutes with the canonical rescaling, rule (5.1)) and §5.4;
Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), Prop. 3.1.
Own bookkeeping (wiring of proved nodes).

`G4UnzipCapRegFreeStmt` is proved by the D29 route:

* **unscaled wedge `(Z, W)`**: the raw cocycle at every folded circle is RC3 of the unzipped
  wedge fields at the pushed circles (`F1.flow_raw_cocycle_of_rc3`), i.e. the wedge flow node
  `F1.WedgeFlowRC3Stmt`, which follows from X-G, X-C and the proved free-field flow nodes
  (`F1.wedgeFlowRC3Stmt_of_x`, `F1.xFlowRC3Stmt_holds`, `F1.XFlowC.xFlowContStmt_holds`);
* **canonical rescaling**: with `a = scaleParam γ Z`, the field of `canonConfig (Z, W)` unzipped
  by `t` is `rescale (U^Z_{a² t}) a` (B3(d) at one time, `unzippedField_canonConfig_fc`, from W-X
  and W-C), and unzipping it further by `u` is `rescale (U^{Z_{a²t}}_{a² u}) a` (B3(d) along the
  flow, `F1.regEq_unzippedField_rescaled`, with the flow regularity `F1.UnscaledFlowRegStmt`);
* **realization**: the `P_*` sample is `avgReg`-equal to `canonical Z` with the rescaled driver
  (`WedgeUnzip.PStarRealizeStmt`), and the Theorem 1.8 sample is a `P_*` sample.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

open WedgeUnzip

theorem regEq_trans' {x y z : FieldSample} (h1 : RegEq x y) (h2 : RegEq y z) : RegEq x z :=
  fun k w => (h1 k w).trans (h2 k w)

theorem regEq_symm' {x y : FieldSample} (h : RegEq x y) : RegEq y x :=
  fun k w => (h k w).symm

theorem regEq_rescale_congr {x y : FieldSample} (h : RegEq x y) (Q a : ℝ) :
    RegEq (rescale x Q a) (rescale y Q a) := by
  have e : rescale x Q a = rescale y Q a :=
    Factorization.coordChange_congr (B3d.avgReg_eq_of_regEq h) _ _
  rw [e]
  exact fun _ _ => rfl

end G4Core
end Thm18Asm
end QuantumZipper
