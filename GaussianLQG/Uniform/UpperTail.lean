import GaussianLQG.Uniform.UpperTail.Comb
import GaussianLQG.Uniform.LowerTail

/-!
# DDDF Proposition 18 with constants uniform in `ξ` (Route U, item U6)

Phase B, packet B-3 (worker PB-U6). Root module of `GaussianLQG/Uniform/UpperTail/`.
Mathematical source: the uniform-constants ledger `blueprint/phaseB/uniform-ledger.tex`, U0, U6,
§5 (rows of `subsec:ledger-upper`) and Findings `fd:step4`, `fd:C1`, `fd:opaque`,
`fd:predicates`, `fd:noise`. Fixed-`ξ` templates (not edited): DDDF20 Prop 18 in
`LQGMetric/Papers/DDDF/` (`P18S2`, `P18S1Conv`, `P18Comb`, `P18Step3`, `P18Step4`, `P18Ell`,
`P18Max`, `P5ULarge`); their helper files (`P18Blocks`, `P18Geom`, `P18Law`, `P18S1Chain`,
`P18S1Geom`, `P18S2Indep`, `P18S2Site`, `P18Scale`, `P18Step2`, `P18Straight`, `P18Strip`,
`P18Zero`) are reused unchanged.

Every statement has its constants chosen before the probability space and before `ξ` (the
ledger's U-form). The long fixed-`ξ` proofs are restated once as lemmas that take their
constants as parameters, with exactly the inequalities the proofs use (`…_of_consts`); the
uniform theorems instantiate them with the template's formulas at `ξs`.

* `UpperTail/Defs.lean`: the uniform predicates `P18Step1PsiU`, `P18Step1U`, `P18Step3U` (ledger
  U0) and their bridges to the fixed-`ξ` predicates.
* `UpperTail/Leaves.lean`: `prop2_tail_R31_W`, `prop5_X3k_tail_W` and the a-priori bound
  `p18_ell_lower_W` (ledger U6), constants before the probability space.
* `UpperTail/Step4.lean`: `p18_step4_unif`, with the ledger's fix (Finding `fd:step4`):
  `c* = 1/(16ξs²)`, `C* = exp(c* A(ξs)⁴/log 2)`. This is the only constant of the chain that is
  unbounded as `ξ ↓ 0` in the template.
* `UpperTail/Step1.lean`: `p18_step1_psi_unif : P18Step1PsiU ξs`, `p18_step1_unif : P18Step1U ξs`.
* `UpperTail/Step3.lean`: `p18_step3_unif_of_cor17 : IfaceCor17U ξs → P18Step3U ξs`.
* `UpperTail/Comb.lean`: `prop18_unif_of_cor17` (Prop 18 from uniform Cor 17).
* this file: the unconditional ledger statements `p18_step3_unif`, `prop18_unif`, and the
  orchestrator's interfaces `ifaceProp18U : IfaceProp18U ξs`, `ifaceStep3U : IfaceStep3U ξs`, for
  every `ξs > 0`, with uniform Cor 17 from `ifaceCor17U` (`GaussianLQG/Uniform/LowerTail.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- **DDDF Prop 18, Step 3 (the a-priori scale bound), uniform in `ξ ∈ (0, ξs]` and in the white
noise** (ledger U6 `p18_step3_unif`): for every `ξs > 0`, `p₀` and, for `p ≤ p₀`, `C` are chosen
before the probability space and before `ξ`, with
`2^{-2ξk} ℓ_{n−k}(φ,p) e^{-C√k} ≤ ℓ_n(φ,p)` for all `k ≤ n`. -/
theorem p18_step3_unif (ξs : ℝ) (hξs : 0 < ξs) : P18Step3U ξs :=
  p18_step3_unif_of_cor17 ξs hξs (ifaceCor17U ξs hξs)

/-- **DDDF Proposition 18 ((4.49), upper tails for `φ`), uniform in `ξ ∈ (0, ξs]` and in the white
noise** (ledger U6 `prop18_unif`): for every `ξs > 0` there is `p₀ > 0` such that for every
`p ∈ (0, p₀]` there are `C, c > 0`, chosen before the probability space and before `ξ`, with
`P(L^{(n)}_{3,1}(φ) ≥ e^s Λ_n(φ,p) ℓ_n(φ,p)) ≤ C e^{-c s²/log s}` for every white noise, every
`ξ ∈ (0, ξs]`, every `n` and every `s > 2`. -/
theorem prop18_unif (ξs : ℝ) (hξs : 0 < ξs) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (s : ℝ), 2 < s →
          P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) *
              ellN ξ W P n (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤
            ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) :=
  prop18_unif_of_cor17 ξs hξs (ifaceCor17U ξs hξs)

/-- **U6 interface**: uniform DDDF Prop 18 gives the orchestrator's `IfaceProp18U ξs`
(`GaussianLQG/Uniform/Interfaces.lean`) for every `ξs > 0`. -/
theorem ifaceProp18U (ξs : ℝ) (hξs : 0 < ξs) : IfaceProp18U ξs :=
  prop18_unif ξs hξs

/-- **U6 interface**: the uniform a-priori scale bound gives the orchestrator's `IfaceStep3U ξs`
(`GaussianLQG/Uniform/Interfaces.lean`) for every `ξs > 0`. -/
theorem ifaceStep3U (ξs : ℝ) (hξs : 0 < ξs) : IfaceStep3U ξs :=
  p18_step3_unif ξs hξs

end Uniform
end GaussianLQG
