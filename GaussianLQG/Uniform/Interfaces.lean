import LQGMetric.Papers.DDDF.LenObs
import LQGMetric.Papers.DDDF.LenBasic

/-!
# Interfaces of the uniform DDDF20 core (Phase B, orchestrator-owned)

The uniform-in-ξ versions of DDDF20 Corollary 17, Proposition 18 (with its a-priori scale bound,
Step 3) and Theorem 20, exactly as in the uniform-constants ledger
(`blueprint/phaseB/uniform-ledger.tex`, statements U5, U6, U9; constants before the probability space
and before ξ). The packets proving U5, U6 and U9 export theorems that imply these propositions. The
consequence packets (U10–U15) take them as hypotheses until then, so the two layers can be developed
in parallel. Internal interfaces, never frozen declarations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise
open scoped ENNReal

namespace GaussianLQG.Uniform

/-- U5 (ledger `cor17_unif`): uniform lower tail of the left–right crossing of `R_{1,3}` relative to the
quantile `ℓ_n(p)`, at every level `p ≤ p₀`. -/
def IfaceCor17U (ξs : ℝ) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (s : ℝ), 0 < s →
        P {ω | lenObs ξ (phiMN W P 0 n) (rectAB 1 3) ω ≤ Real.exp (-s) * ellN ξ W P n (ENNReal.ofReal p)}
          ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2))

/-- U6 (ledger `prop18_unif`): uniform upper tail of the crossing of `R_{3,1}` relative to
`Λ_n(p) ℓ_n(p)`, at every level `p ≤ p₀`. -/
def IfaceProp18U (ξs : ℝ) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) ξs, ∀ (n : ℕ) (s : ℝ), 2 < s →
        P {ω | Real.exp s * LambdaN ξ W P n (ENNReal.ofReal p) * ellN ξ W P n (ENNReal.ofReal p) ≤
            lenObs ξ (phiMN W P 0 n) (rectAB 3 1) ω} ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s))

/-- U6 (ledger `p18_step3_unif`): the uniform a-priori scale bound
`2^{-2ξk} ℓ_{n-k}(p) e^{-C√k} ≤ ℓ_n(p)`. -/
def IfaceStep3U (ξs : ℝ) : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) ξs, ∀ n k : ℕ, k ≤ n →
        (2 : ℝ) ^ (-(2 * ξ * k)) * ellN ξ W P (n - k) (ENNReal.ofReal p) * Real.exp (-(C * Real.sqrt k))
          ≤ ellN ξ W P n (ENNReal.ofReal p)

/-- U9 (ledger `thm20_unif`, the φ part): Theorem 20 of DDDF20 uniformly in `ξ ∈ (0, 1/8]`,
`Λ_n(φ, p) ≤ B` for every level `p ≤ p₀`. -/
def IfaceThm20U : Prop :=
  ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p : ℝ, 0 < p → p ≤ p₀ → ∃ B : ℝ,
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) (1 / 8), ∀ n : ℕ, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B

end GaussianLQG.Uniform
