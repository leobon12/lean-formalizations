import GaussianLQG.Field.Pairing
import GaussianLQG.Medians.LawM

/-!
# Discharged interface propositions (orchestrator integration)

Each theorem here closes an interface proposition of `Core/Interfaces.lean` for every `Setup`, by
combining packets that were proved separately.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace GaussianLQG.Setup

variable (S : Setup)

/-- Blueprint Lemma `lem:law-M` for every `Setup`: W11's `Setup.lawM` with its five hypotheses
discharged by W7 (blueprint Lemma `lem:field`(a),(c), Lemma `lem:H-continuity`(c), the law of
`H(0,0)`). -/
theorem lawM_holds : S.LawM :=
  S.lawM (fun _ hμ => ae_pairing_shiftBy S.frame hμ) map_shiftBy_absolutelyContinuous
    S.ae_bddBelow_H_dyadic S.measurable_H S.h00Law

end GaussianLQG.Setup
