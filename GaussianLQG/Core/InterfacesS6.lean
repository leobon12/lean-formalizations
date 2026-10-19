import GaussianLQG.Core.MainDefs
import LQGMetric.Statement.LFPP

/-!
# Interface propositions for Phase B, the proof of (S6) (internal)

`LFPPUniformMoments c` is the statement (★) of Route U (planning/audits/B1-S6-feasibility.md, U15):
uniform moment bounds for Liouville first passage percolation at dyadic scales `ε = 2⁻ⁿ`, normalized
by deterministic constants `c γ n`, under the law of the normalized whole-plane GFF. The passage to
the limit (U16) turns it into `UniformMomentInput` for the canonical metric. These are implementation
interfaces, never frozen declarations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG

/-- (★): for every `p ≥ 1` there is `γ_p > 0` such that for every compact `K` and `δ > 0` the Hölder
constant and the inverse separated distance of `X^{(n)} := (c γ n)⁻¹ D^{2⁻ⁿ}_h` (LFPP with
`ξ = ξ_γ`) have `p`-th moments bounded uniformly in `γ ∈ (0, γ_p]` and `n ≥ 1`. -/
def LFPPUniformMoments (c : ℝ → ℕ → ℝ) : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∃ γp : ℝ, 0 < γp ∧ ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ γ ∈ Ioc (0 : ℝ) γp, ∀ n : ℕ, 1 ≤ n →
      (∫⁻ g, holderConst (fun z => (c γ n)⁻¹ *
          LQGMetric.lfppDist (LQGMetric.xiGamma γ) ((2 : ℝ)⁻¹ ^ n) g z) K ^ p
        ∂LQGMetric.normGFFLaw) ≤ C ∧
      (∫⁻ g, (sepInf (fun z => (c γ n)⁻¹ *
          LQGMetric.lfppDist (LQGMetric.xiGamma γ) ((2 : ℝ)⁻¹ ^ n) g z) K δ)⁻¹ ^ p
        ∂LQGMetric.normGFFLaw) ≤ C

end GaussianLQG
