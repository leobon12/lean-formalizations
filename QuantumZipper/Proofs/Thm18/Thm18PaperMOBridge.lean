import QuantumZipper.Statements.Thm18PaperMO
import QuantumZipper.Proofs.Thm18.RT6MODefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bridge: the Statements-layer `Paper18.theorem1_8PaperMO` is `R18.theorem1_8PaperMO` (D91)

Decision D91 (statement placement): the target of Theorem 1.8 (Sheffield, arXiv:1012.4797, p. 26)
is stated in `Statements/Thm18PaperMO.lean` with verbatim copies of the proofs-layer definitions.
Each copy is definitionally equal to its original; the headline is
`Paper18.theorem1_8PaperMO_iff_R18`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Paper18

theorem offConfig_eq_R18 : offConfig = R18.offConfig := rfl

theorem zipLenDownMA_eq_R18 : zipLenDownMA = R18.zipLenDownMA := rfl

theorem zipLenUpOA_eq_R18 : zipLenUpOA = R18.zipLenUpOA := rfl

theorem zipLenMO_eq_R18 : zipLenMO = R18.zipLenMO := by
  funext γ ℓ
  unfold zipLenMO R18.zipLenMO
  rw [zipLenUpOA_eq_R18, offConfig_eq_R18, zipLenDownMA_eq_R18]

/-- **Bridge (D91).** The Statements-layer form of Theorem 1.8 is the proofs-layer target. -/
theorem theorem1_8PaperMO_iff_R18 : theorem1_8PaperMO ↔ R18.theorem1_8PaperMO := by
  unfold theorem1_8PaperMO R18.theorem1_8PaperMO theorem1_8_zipperStationarityPaperMO
    R18.theorem1_8_zipperStationarityPaperMO
  rw [zipLenMO_eq_R18, zipLenDownMA_eq_R18]

theorem theorem1_8PaperMO_of_R18 (h : R18.theorem1_8PaperMO) : theorem1_8PaperMO :=
  theorem1_8PaperMO_iff_R18.2 h

end Paper18
end QuantumZipper
