import GaussianLQG.Uniform.Holder
import GaussianLQG.Uniform.CoreDone

/-!
# U12, unconditionally

Phase B, packet PB-U12. The interfaces U10 (`IfaceMomentsLambdaU`) and U11 (`IfaceScaleU`) hold
unconditionally (`ifaceMomentsLambdaU_holds`, `ifaceScaleU_holds`,
`GaussianLQG/Uniform/CoreDone.lean`), so U12 (`holder_moment_unif`, `holder_moment_unit`) and the
interface `IfaceHolderMomentU` hold without hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- **U12** (ledger `holder_moment_unif`), unconditionally. -/
theorem holder_moment_unif_holds (q : ℝ) (hq : 1 ≤ q) : ∃ ξq : ℝ, 0 < ξq ∧ ∀ R : ℝ, 0 < R →
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ ξ ∈ Set.Ioc (0 : ℝ) ξq, ∀ n : ℕ,
          ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
            (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) (boxOut R) z.1 z.2).toReal)
            (boxIn R) ^ q ∂P ≤ C :=
  holder_moment_unif ifaceMomentsLambdaU_holds ifaceScaleU_holds q hq

/-- **U12a** (unit square), unconditionally. -/
theorem holder_moment_unit_holds (q : ℝ) (hq : 1 ≤ q) : ∃ ξq : ℝ, 0 < ξq ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) ξq, ∀ n : ℕ,
        ∫⁻ ω, holderConst (fun z => (lambdaN ξ W P n)⁻¹ *
          (LFPP.lfppDOn ξ (fun x => phiMN W P 0 n x ω) Blueprint.closedUnitSquare z.1 z.2).toReal)
          Blueprint.closedUnitSquare ^ q ∂P ≤ C :=
  holder_moment_unit ifaceMomentsLambdaU_holds ifaceScaleU_holds q hq

/-- **The interface `IfaceHolderMomentU`**, unconditionally. -/
theorem ifaceHolderMomentU_holds : IfaceHolderMomentU :=
  ifaceHolderMomentU ifaceMomentsLambdaU_holds ifaceScaleU_holds

end Uniform
end GaussianLQG
