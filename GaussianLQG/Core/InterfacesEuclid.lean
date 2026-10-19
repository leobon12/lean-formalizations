import GaussianLQG.Core.Setup

/-!
# Interface propositions for Section 5 of the blueprint (internal)

The conclusions of Lemma `lem:euclidean` and Lemma `lem:energy-approx` for an arbitrary `Setup`.
The Section 5 packet proves them; the Section 6 packet consumes them as hypotheses. These are
implementation interfaces, never frozen declarations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace GaussianLQG.Setup

variable (S : Setup)

/-- `𝖤_γ(R) = sup_{z,w ∈ B̄_R(0)} |e^{-b_γ} D^γ(z,w) - |z-w||` (blueprint Lemma `lem:euclidean`). -/
def euclidErr (γ R : ℝ) (ω : Coord) : ℝ≥0∞ :=
  ⨆ z ∈ Metric.closedBall (0 : ℂ) R, ⨆ w ∈ Metric.closedBall (0 : ℂ) R,
    ENNReal.ofReal |Real.exp (-S.b γ) * (S.D γ ω).1 (z, w) - ‖z - w‖|

/-- Blueprint Lemma `lem:euclidean`: for `R ≥ 1` and `p ≥ 1`, `E[𝖤_γ(R)^p] ≤ C ξ_γ^{p/2}` for small
`γ` (that is, `‖𝖤_γ(R)‖_p ≤ C' ξ_γ^{1/2}`). -/
def EuclidApprox : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∀ p : ℝ, 1 ≤ p → ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs,
    (∫⁻ ω, S.euclidErr γ R ω ^ p ∂stdP) ≤ ENNReal.ofReal (C * S.ξ γ ^ (p / 2))

/-- Blueprint Lemma `lem:energy-approx`: for compact `K`, `δ > 0` and `p ≥ 1` there are, for small `γ`,
measurable `Y_γ` with `E[Y_γ^p] ≤ C ξ_γ^{p/24}` such that almost surely, for all `z, w ∈ K` with
`|z - w| ≥ δ` and every geodesic `η` from `z` to `w`, the length measure `ν_η` is regular and
`‖ν_η - λ_{z,w}‖_*² ≤ Y_γ²`. -/
def EnergyApprox : Prop :=
  ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ → ∀ p : ℝ, 1 ≤ p →
    ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∃ Y : Coord → ℝ≥0∞, Measurable Y ∧
      (∫⁻ ω, Y ω ^ p ∂stdP) ≤ ENNReal.ofReal (C * S.ξ γ ^ (p / 24)) ∧
      ∀ᵐ ω ∂stdP, ∀ z ∈ K, ∀ w ∈ K, δ ≤ ‖z - w‖ → ∀ η : C(unitInterval, ℂ),
        LQGMetric.Blueprint.IsGeod01 (S.D γ ω) z w η →
          IsRegular (lengthMeasure η) ∧
            ENNReal.ofReal (energy (lengthMeasure η) (lengthMeasure η) -
              2 * energy (lengthMeasure η) (segMeasure z w) + energy (segMeasure z w) (segMeasure z w))
              ≤ Y ω ^ 2

end GaussianLQG.Setup
