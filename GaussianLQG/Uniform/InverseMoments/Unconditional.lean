import GaussianLQG.Uniform.InverseMoments
import GaussianLQG.Uniform.CoreDone

/-!
# Uniform inverse separated-distance moments, unconditionally (Route U, item U13)

`inv_moment_unif` (`GaussianLQG/Uniform/InverseMoments.lean`) takes the consequence interfaces U10
(`IfaceMomentsLambdaU`) and U11 (`IfaceScaleU`) as hypotheses. Both are proved
(`ifaceMomentsLambdaU_holds`, `ifaceScaleU_holds`, `GaussianLQG/Uniform/CoreDone.lean`), so the
ledger statement U13 (b), in the `ℝ≥0∞` form of audit B-0b (S-1, M-4), holds without hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GaussianLQG
namespace Uniform

open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise

/-- **Ledger U13 (b), `inv_moment_unif`, unconditionally** (witness `ξq' = min (1/8) (1/q)`). -/
theorem inv_moment_unif_holds (q : ℝ) (hq : 1 ≤ q) : ∃ ξq' : ℝ, 0 < ξq' ∧
    ∀ K₀ : Set ℂ, IsCompact K₀ → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ ξ ∈ Set.Ioc (0 : ℝ) ξq', ∀ n : ℕ,
      ∫⁻ ω, (ENNReal.ofReal (lambdaN ξ W P n) /
          ⨅ b ∈ blockSet K₀ (kDelta δ), ⨅ j ∈ T20D.shortJ (kDelta δ) b,
            crossLenIn ξ (fun x => phiMN W P 0 n x ω) (T20D.RS (kDelta δ) j)
              (T20D.RS₁ (kDelta δ) j) (T20D.RS₂ (kDelta δ) j)) ^ q ∂P ≤ C :=
  inv_moment_unif ifaceMomentsLambdaU_holds ifaceScaleU_holds q hq

/-- **U13 with the explicit range `ξ ∈ (0, min (1/8) (1/q)]`, unconditionally.** -/
theorem inv_moment_unif_le_holds (q : ℝ) (hq : 1 ≤ q) (K₀ : Set ℂ) (hK₀ : IsCompact K₀) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ ξ ∈ Set.Ioc (0 : ℝ) (min (1 / 8) (1 / q)), ∀ n : ℕ,
      ∫⁻ ω, (ENNReal.ofReal (lambdaN ξ W P n) /
          ⨅ b ∈ blockSet K₀ (kDelta δ), ⨅ j ∈ T20D.shortJ (kDelta δ) b,
            crossLenIn ξ (fun x => phiMN W P 0 n x ω) (T20D.RS (kDelta δ) j)
              (T20D.RS₁ (kDelta δ) j) (T20D.RS₂ (kDelta δ) j)) ^ q ∂P ≤ C :=
  inv_moment_unif_le ifaceMomentsLambdaU_holds ifaceScaleU_holds q hq K₀ hK₀ δ hδ hδ1

end Uniform
end GaussianLQG
