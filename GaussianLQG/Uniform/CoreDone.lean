import GaussianLQG.Uniform.Thm20.Unconditional
import GaussianLQG.Uniform.UpperTail
import GaussianLQG.Uniform.Consequences

/-!
# The uniform DDDF20 core and its consequences, discharged (orchestrator integration)

Uniform Corollary 17 (`ifaceCor17U`), Proposition 18 and Step 3 (`ifaceProp18U`, `ifaceStep3U`) and
Theorem 20 (`ifaceThm20U_holds`) are proved, so the consequence interfaces U10–U11 hold
unconditionally.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace GaussianLQG.Uniform

/-- Ledger U10 (tails relative to `λ_n`), unconditionally. -/
theorem ifaceTailsLambdaU_holds : IfaceTailsLambdaU :=
  ifaceTailsLambdaU (ifaceProp18U (1 / 8) (by norm_num)) ifaceThm20U_holds

/-- Ledger U10 (moments relative to `λ_n`), unconditionally. -/
theorem ifaceMomentsLambdaU_holds : IfaceMomentsLambdaU :=
  ifaceMomentsLambdaU (ifaceProp18U (1 / 8) (by norm_num)) ifaceThm20U_holds

/-- Ledger U11 (scale relations), unconditionally. -/
theorem ifaceScaleU_holds : IfaceScaleU :=
  ifaceScaleU (ifaceProp18U (1 / 8) (by norm_num)) (ifaceStep3U (1 / 8) (by norm_num))
    ifaceThm20U_holds

end GaussianLQG.Uniform
