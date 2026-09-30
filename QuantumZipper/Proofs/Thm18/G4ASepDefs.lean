import QuantumZipper.Proofs.Thm18.G4CoreDefs3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 Core A-sep (task G4C-ASEP): the two sub-nodes

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1).
Decision D57 (`handoff/G4-CORE.md` §6). `G4DriverPushSepAllStmt` (`G4CoreDefs3.lean`) has four
conjuncts at each separated circle: two exactness conjuncts (probabilistic, RC3 of the later field
at circles pushed by `f_τ ∘ f_{τ'}⁻¹(a ·)`) and two log-integrability conjuncts. The latter reduce
(`G4ASepLog.lean`, chain rule `deriv_fwdMapInv_mul_backDrv` and the Koebe bound
`G1.integrable_log_norm_deriv_foldedCircle_of_injOn` for `f_{τ'}⁻¹(a ·)`) to one deterministic
Loewner fact, `BackLogSepStmt`: for a reverse Loewner map `R = revMap V T` and a folded circle at
positive distance from its hull, `log ‖R' ∘ R⁻¹‖` is integrable on the circle. (True for every
continuous driver: `R⁻¹` extends conformally across the real points at positive distance from the
hull by Schwarz reflection — Lawler, *Conformally Invariant Processes in the Plane*, §4.1 — so the
integrand is bounded on the support of the circle; cf. `RevMapExtension.exists_revMapExt_extension`.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- **(Deterministic Loewner node.)** For a continuous driver `V` (`V 0 = 0`), `T ≥ 0`, and a
folded circle carried by `R(ℍ)`, `R = revMap V T`, with some `δ`-thickening of the hull
`revHull V T` null, `log ‖R'(R⁻¹ w)‖` is integrable on the circle. -/
def BackLogSepStmt : Prop :=
  ∀ V : ℝ → ℝ, Continuous V → V 0 = 0 → ∀ T : ℝ, 0 ≤ T → ∀ (d : ℂ) (r : ℝ), 0 < r →
    foldedCircle d r (revMap V T '' H)ᶜ = 0 →
    (∃ δ : ℝ, 0 < δ ∧ foldedCircle d r (Metric.thickening δ (revHull V T)) = 0) →
    Integrable (fun w => Real.log ‖deriv (revMap V T) (revMapInv V T w)‖) (foldedCircle d r)

end G4Core
end Thm18Asm
end QuantumZipper
