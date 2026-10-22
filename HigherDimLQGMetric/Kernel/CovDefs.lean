import HigherDimLQGMetric.Frozen.ConvKernelEps
import HigherDimLFPP.Field.Measures

/-!
# Measure convolution and the covariance statement of [1, Lemma 2.9]

These declarations reproduce the audited MA5 surface.  The theorem is proved
in a later covariance module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

def measConv (κ : Rd d → ℝ) (ε : ℝ) (μ : Measure (Rd d)) (x : Rd d) : ℝ :=
  ∫ z, convKernelEps κ ε (x - z) ∂μ

def convLogCov (κ : Rd d → ℝ) (ε : ℝ)
    (μ ν μ' ν' : Measure (Rd d)) : ℝ :=
  ∫ x, ∫ y, (measConv κ ε μ x - measConv κ ε ν x) *
    (-Real.log ‖x - y‖) *
    (measConv κ ε μ' y - measConv κ ε ν' y)

/-- MA5's exact covariance proposition, with bounded-support finite measures. -/
def L1d_cov : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
    ∀ ε : ℝ, 0 < ε →
    ∀ (μ ν μ' ν' : Measure (Rd d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      [IsFiniteMeasure μ'] [IsFiniteMeasure ν'],
      μ.real univ = ν.real univ → μ'.real univ = ν'.real univ →
      (∃ D : ℝ, (∀ᵐ z ∂μ, ‖z‖ ≤ D) ∧ (∀ᵐ z ∂ν, ‖z‖ ≤ D) ∧
        (∀ᵐ z ∂μ', ‖z‖ ≤ D) ∧ (∀ᵐ z ∂ν', ‖z‖ ≤ D)) →
      HigherDimLFPP.IsPairable κ (Ioi ε) μ ν ∧
        HigherDimLFPP.IsPairable κ (Ioi ε) μ' ν' ∧
        HigherDimLFPP.scaleCov κ (Ioi ε) μ ν μ' ν' =
          convLogCov κ ε μ ν μ' ν'

end HigherDimLQGMetric
