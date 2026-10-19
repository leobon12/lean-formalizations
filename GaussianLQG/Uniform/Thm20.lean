import GaussianLQG.Uniform.Thm20.Step5
import LQGMetric.Papers.DDDF.S6P21

/-!
# DDDF Theorem 20 uniformly in `ξ ∈ (0, 1/8]` (Route U, ledger U9)

Phase B, packet PB-U9 (ledger packet B-6). Uniform-constants ledger
`blueprint/phaseB/uniform-ledger.tex`, statement U9, §`subsec:ledger-T20`, Findings `fd:step5`,
`fd:opaque`, `fd:predicates`; corrected Appendix A of the blueprint, Lemma A.2.

`thm20_unif`: for the parameters `S6.psiQ₁` of `ψ` (`r₀ = 1/12`, `ε₀ = 1/4`; `PsiSmall` by
`S6.psiSmall_psiQ₁`), there is `p₀ > 0` and, for every `p ≤ p₀`, a bound `B` chosen before the
probability space and before `ξ`, such that for every white noise, every `ξ ∈ (0, 1/8]` and every
`n`: `Λ_n(φ, p) ≤ B`, `Λ_n(ψ, p/2) ≤ B` and `Var log L^{(n)}_{1,1}(ψ) ≤ B`.

The only inputs are the uniform Cor 17 and Prop 18 (`IfaceCor17U (1/8)`, `IfaceProp18U (1/8)`,
`GaussianLQG/Uniform/Interfaces.lean`, ledger U5 and U6), which enter the template only through
the ratio moment (5.66) (`LQGMetric/Papers/DDDF/T20BRect.lean:88,121`). Condition (T) is
`conditionTU_small_all` (U8, `GaussianLQG/Uniform/ConditionT.lean`; it replaces the `∃`-after-`ξ`
input of `LQGMetric/Papers/DDDF/T20CMain.lean:164`). The chain:

1. pathwise bound, uniform (`t20Step4PathwiseU`: circuit gluing, (5.61)–(5.64));
2. visited blocks (`t20_step4_visited_of_pathwise_unif`), then `T20Step4U`;
3. Steps 1–3 and 5 with the uniform constants and the data-free bound of Step 5
   (`thm20_unif_of`, `GaussianLQG/Uniform/Thm20/Step5.lean`).

`ifaceThm20U`: the interface `IfaceThm20U` (the `φ` part).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

lemma psiQ₁_ε₀ : S6.psiQ₁.ε₀ = 1 / 4 := rfl

/-- **Step 4 of DDDF Theorem 20 for `S6.psiQ₁`, uniform in `ξ ∈ (0, 1/8]`** (ledger U0, U9),
from the uniform Cor 17 and Prop 18. -/
theorem t20Step4U_psiQ₁ (h17 : IfaceCor17U (1 / 8)) (h18 : IfaceProp18U (1 / 8)) :
    T20Step4U (1 / 8) S6.psiQ₁ := by
  have hε : S6.psiQ₁.ε₀ < 1 / 2 := by rw [psiQ₁_ε₀]; norm_num
  have hε' : S6.psiQ₁.ε₀ ≤ 1 := by rw [psiQ₁_ε₀]; norm_num
  exact t20Step4U_of_visitedU (t20_step4_visited_of_pathwise_unif S6.psiQ₁ hε
    (conditionTU_small_all.{0} S6.psiQ₁) (t20Step4PathwiseU.{0} S6.psiQ₁ hε' (by norm_num))
    h17 h18)

/-- **DDDF Theorem 20, uniformly in `ξ ∈ (0, 1/8]` and in the white noise** (ledger U9,
`thm20_unif`; blueprint Lemma A.2): `p₀`, and for `p ≤ p₀` the bound `B`, are chosen before the
probability space and before `ξ`. Inputs: the uniform Cor 17 and Prop 18 (ledger U5, U6). -/
theorem thm20_unif (h17 : IfaceCor17U (1 / 8)) (h18 : IfaceProp18U (1 / 8)) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ B : ℝ,
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) (1 / 8), ∀ n : ℕ,
        LambdaN ξ W P n (ENNReal.ofReal p) ≤ B ∧
        LambdaNPsi ξ S6.psiQ₁ W P n (ENNReal.ofReal (p / 2)) ≤ B ∧
        Var[L24.logLenPsi ξ S6.psiQ₁ W P n; P] ≤ B :=
  thm20_unif_of S6.psiQ₁ S6.psiSmall_psiQ₁ (t20Step4U_psiQ₁ h17 h18)

/-- **The interface `IfaceThm20U`** (ledger U9, the `φ` part of `thm20_unif`), from the uniform
Cor 17 and Prop 18. -/
theorem ifaceThm20U (h17 : IfaceCor17U (1 / 8)) (h18 : IfaceProp18U (1 / 8)) : IfaceThm20U := by
  obtain ⟨p₀, hp₀, h⟩ := thm20_unif h17 h18
  refine ⟨p₀, hp₀, fun p hp hpp => ?_⟩
  obtain ⟨B, hB⟩ := h p hp hpp
  exact ⟨B, fun hW ξ hξ n => (hB hW ξ hξ n).1⟩

end Uniform
end GaussianLQG
