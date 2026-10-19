import GaussianLQG.Uniform.Thm20
import GaussianLQG.Uniform.Shapes
import GaussianLQG.Uniform.UpperTail

/-!
# Theorem 20 and the shapes, uniform in `ξ`, without hypotheses

Phase B, packet PB-U9. `thm20_unif`, `ifaceThm20U` (`GaussianLQG/Uniform/Thm20.lean`) and
`shapes_unif` (`GaussianLQG/Uniform/Shapes.lean`) take the uniform Cor 17 and Prop 18 as the
interfaces `IfaceCor17U`, `IfaceProp18U`. These are theorems: `ifaceCor17U`
(`GaussianLQG/Uniform/LowerTail.lean`, packet PB-U5) and `ifaceProp18U`
(`GaussianLQG/Uniform/UpperTail.lean`, packet PB-U6). This module discharges them; it is kept
separate so that the conditional statements do not depend on those files.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- **DDDF Theorem 20, uniformly in `ξ ∈ (0, 1/8]` and in the white noise** (ledger U9,
`thm20_unif`, with its two interface inputs discharged). -/
theorem thm20_unif_holds :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ B : ℝ,
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) (1 / 8), ∀ n : ℕ,
        LambdaN ξ W P n (ENNReal.ofReal p) ≤ B ∧
        LambdaNPsi ξ S6.psiQ₁ W P n (ENNReal.ofReal (p / 2)) ≤ B ∧
        Var[L24.logLenPsi ξ S6.psiQ₁ W P n; P] ≤ B :=
  thm20_unif (ifaceCor17U (1 / 8) (by norm_num)) (ifaceProp18U (1 / 8) (by norm_num))

/-- **The interface `IfaceThm20U` holds** (ledger U9, the `φ` part of `thm20_unif`). -/
theorem ifaceThm20U_holds : IfaceThm20U :=
  ifaceThm20U (ifaceCor17U (1 / 8) (by norm_num)) (ifaceProp18U (1 / 8) (by norm_num))

/-- **The finite family of shapes, uniform in `ξ ∈ (0, ξs]`** (ledger U7, `shapes_unif`, with
its two interface inputs discharged). -/
theorem shapes_unif_holds (ξs : ℝ) (hξs : 0 < ξs) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (a b : ℝ),
        (a, b) ∈ ({(1, 3), (1, 1), (2, 1), (3, 1)} : Set (ℝ × ℝ)) →
        (∀ s : ℝ, 0 < s → P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤
            Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2))) ∧
        (∀ s : ℝ, 2 < s → P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) *
            ellN ξ W P n (ENNReal.ofReal p) ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω} ≤
          ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s))) :=
  shapes_unif ξs hξs (ifaceCor17U ξs hξs) (ifaceProp18U ξs hξs)

end Uniform
end GaussianLQG
