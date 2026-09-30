import QuantumZipper.Proofs.Zipper.BaseFin2ULRad
import QuantumZipper.Proofs.Zipper.BaseFin2ULNrm
import QuantumZipper.Proofs.Zipper.BaseFin2ULG0Pt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1-UL: assembly

`BaseUnitLenMomStmt` from the two remaining single estimates: the exponential moment of the
chart-`1` normalization constant at `ϖ₀ = fc(0,1)` (`BaseULConstStmt`) and the first moments of
the `Γ⁰` boundary approximations (`BaseULGamma0MomStmt`); the tail of `|O^±_1|` is proved
(`baseULRadStmt_holds`). Own bookkeeping.
-/

namespace QuantumZipper
namespace BaseFin2

theorem baseUnitLenMom_of_const_gamma0 (hC : BaseULConstStmt) (hG : BaseULGamma0MomStmt) :
    BaseUnitLenMomStmt :=
  baseUnitLenMom_of_parts hC baseULRadStmt_holds (baseULNrm_of_gamma0 hG)

/-- `BaseUnitLenMomStmt` from the normalization-constant moment alone
(`BaseULGamma0MomStmt` is proved: `baseULGamma0MomStmt_holds`). -/
theorem baseUnitLenMom_of_const (hC : BaseULConstStmt) : BaseUnitLenMomStmt :=
  baseUnitLenMom_of_const_gamma0 hC baseULGamma0MomStmt_holds

end BaseFin2
end QuantumZipper
