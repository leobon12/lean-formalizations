import QuantumZipper.Proofs.Section5.Prop16BdryMom
import QuantumZipper.Proofs.Section5.Prop16BdryMomGauss
import QuantumZipper.Proofs.Section5.Prop16PalmGlobal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′: the boundary moment, uniform integrability and `L¹` nodes (proved)

* `prop16BdryMomGaussStmt_holds` (`lintegral_expV_bdryMom_le`, `Prop16BdryMomGauss.lean`);
* `prop16BdryMomStmt_holds : Prop16BdryMomStmt` (`prop16BdryMomStmt_of_gauss`);
* `prop16BdryUIStmt_holds`, `prop16BdryL1LocStmt_holds`, `prop16BdryL1Stmt_holds`;
* `prop16PalmGlobalStmt_holds_bdryMom : Prop16PalmGlobalStmt`
  (`prop16PalmGlobalStmt_of_bdryL1Loc`).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
proof of Prop. 1.2 and §6; Sheffield arXiv:1012.4797, Prop. 1.6 (p. 25). See
`Prop16BdryMom.lean` for the proof route.
-/

namespace QuantumZipper

namespace Prop16Asm

/-- **Node B′-MOM-GAUSS (proved).** -/
theorem prop16BdryMomGaussStmt_holds : Prop16BdryMomGaussStmt :=
  fun hgeo ht hs0 hs01 hs1 hr'r hD hR _ _ _ _ _ _ _ _ hY hXf hgh hgm hrep lam =>
    lintegral_expV_bdryMom_le hgeo ht hs0 hs01 hs1 hr'r hD hR hY hXf hgh hgm hrep lam

/-- **Node B′-MOM (proved): uniform `p > 1` moment of the boundary masses near the free arc.** -/
theorem prop16BdryMomStmt_holds : Prop16BdryMomStmt :=
  prop16BdryMomStmt_of_gauss prop16BdryMomGaussStmt_holds

/-- **Node `Prop16BdryL1LocStmt` (proved).** -/
theorem prop16BdryL1LocStmt_holds : Prop16BdryL1LocStmt :=
  prop16BdryL1LocStmt_of_mom prop16BdryMomStmt_holds

/-- **The global window Palm formula (proved).** -/
theorem prop16PalmGlobalStmt_holds_bdryMom : Prop16PalmGlobalStmt :=
  prop16PalmGlobalStmt_of_bdryL1Loc prop16BdryL1LocStmt_holds

end Prop16Asm

end QuantumZipper
