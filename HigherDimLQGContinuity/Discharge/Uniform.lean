import HigherDimLQGContinuity.UnifNondeg.Main
import HigherDimLQGContinuity.UnifTight.HolderTight
import HigherDimLQGContinuity.UnifBase.ExpRate
import HigherDimLQGContinuity.MomentsW1.UpperMoment

/-!
# Discharge of the uniform-in-ξ DGZ interfaces (orchestrator; rulings N6, N28)

Appendix A's interfaces I6–I10 are proved by packets U3 (`uCor52`), U4 (`uDistInf`, `uHolderTight_of_quantComp`) and U5
(`uQuantComp`, `uNondeg`). The Hölder tightness I8 is normalized by the median, so it is composed here from the quantile
comparability I7 (ruling N28: U5 produces I7 without assuming I8).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd IsLFPPKernel)

variable {d : ℕ}

/-- **I8** (`UHolderTightShape`), from U4's `uHolderTight_of_quantComp` and U5's `uQuantComp`. -/
theorem uHolderTight (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) : UHolderTightShape d κ :=
  uHolderTight_of_quantComp hd hκ (uQuantComp hd hκ)

/-- The five uniform DGZ interfaces I6–I10 at once. -/
theorem uniformDGZ_holds (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) :
    UCor52Shape d κ ∧ UQuantCompShape d κ ∧ UHolderTightShape d κ ∧ UNondegShape d κ ∧ UDistInfShape d κ :=
  ⟨uCor52 hd hκ, uQuantComp hd hκ, uHolderTight hd hκ, uNondeg hd hκ, uDistInf hd hκ⟩

/-- **I11** (`WNUpperMomentShape`, W1), from A2's `wnUpperMoment` with its interface inputs discharged. -/
theorem wnUpperMoment_holds (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) : WNUpperMomentShape d κ :=
  wnUpperMoment hd hκ (uExpRate hd hκ) (uCor52 hd hκ) (uQuantComp hd hκ) (uNondeg hd hκ)

end HigherDimLQGContinuity
