import GaussianLQG.Uniform.Interfaces

/-!
# Interfaces of the consequence layer (Phase B, orchestrator-owned)

The ledger statements U10 (tails and moments of crossing lengths relative to `λ_n`) and U11 (scale
relations) for `ξ ∈ (0, 1/8]`, with constants before the probability space
(`blueprint/phaseB/uniform-ledger.tex`). The packet proving U10–U11 exports theorems implying these
propositions; the U12/U13 packets take them as hypotheses meanwhile. Internal interfaces only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise
open scoped ENNReal

namespace GaussianLQG.Uniform

/-- The four rectangle shapes of the ledger (U7): `R_{1,3}, R_{1,1}, R_{2,1}, R_{3,1}`. -/
def shapeSet : Set (ℝ × ℝ) := {(1, 3), (1, 1), (2, 1), (3, 1)}

/-- U10 (ledger `tails_lambda_unif`): two-sided tails of the crossing lengths relative to `λ_n`. -/
def IfaceTailsLambdaU : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) (1 / 8), ∀ (n : ℕ) (a b : ℝ), (a, b) ∈ shapeSet → ∀ s : ℝ, 2 < s →
        P {ω | Real.exp s * lambdaN ξ W P n ≤ lenObs ξ (phiMN W P 0 n) (rectAB a b) ω}
            ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2 / Real.log s)) ∧
          P {ω | lenObs ξ (phiMN W P 0 n) (rectAB a b) ω ≤ Real.exp (-s) * lambdaN ξ W P n}
            ≤ ENNReal.ofReal (C * Real.exp (-c * s ^ 2))

/-- U10 (ledger `moments_lambda_unif`): all positive and negative moments of `L_n(R)/λ_n`. -/
def IfaceMomentsLambdaU : Prop :=
  ∀ q : ℝ, 1 ≤ q → ∃ C : ℝ,
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) (1 / 8), ∀ (n : ℕ) (a b : ℝ), (a, b) ∈ shapeSet →
        (∫⁻ ω, ENNReal.ofReal ((lenObs ξ (phiMN W P 0 n) (rectAB a b) ω / lambdaN ξ W P n) ^ q) ∂P)
            ≤ ENNReal.ofReal C ∧
          (∫⁻ ω, ENNReal.ofReal ((lambdaN ξ W P n / lenObs ξ (phiMN W P 0 n) (rectAB a b) ω) ^ q) ∂P)
            ≤ ENNReal.ofReal C

/-- U11 (ledger `scale_unif`): the scale relations (a)–(d) for `λ_n`. -/
def IfaceScaleU : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
      ∀ ξ ∈ Set.Ioc (0 : ℝ) (1 / 8), ∀ n : ℕ,
        (∀ k : ℕ, k ≤ n → lambdaN ξ W P (n - k) ≤
            C * (2 : ℝ) ^ (2 * ξ * k) * Real.exp (C * Real.sqrt k) * lambdaN ξ W P n) ∧
        Real.exp (-C) * lambdaN ξ W P n ≤ lambdaN ξ W P (n + 1) ∧
        lambdaN ξ W P (n + 1) ≤ Real.exp C * lambdaN ξ W P n ∧
        Real.exp (-(ξ * (C + 2 * (n + 1) * Real.log 2))) ≤ lambdaN ξ W P n ∧
        lambdaN ξ W P n ≤ 3 * Real.exp (ξ ^ 2 * n * Real.log 2 / 2)

end GaussianLQG.Uniform
