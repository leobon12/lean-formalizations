-- Frozen anchor (definition, spec_IsContLocalMartingaleBefore_v1). Orchestrator-owned: never edit by hand; see planning/RULINGS.md R5, R6.
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace InteractingSLE

/-- **`X` is a continuous local martingale on `[0, ζ)`** in the filtration `𝓕` (Specification Theorem 2.4, p. 35:
"`𝔥_t(z)` evolves as a continuous local martingale in `t` … until the time `z` is absorbed", R109: and before the
continuation threshold; Theorem 2.6, p. 40): almost surely the path of `X` is continuous on `[0, ζ)`, and there are
`𝓕`-stopping times `σ_n`, each either `0` or strictly below `ζ`, such that almost surely every time before `ζ` lies
below `σ_n` for all large `n`, and every process `t ↦ 1_{σ_n > 0} X_{t ∧ σ_n}` is an `𝓕`-martingale (Mathlib's
localization convention `Locally`, with the indicator of `{σ_n > 0}`). Only the values of `X` strictly before `ζ` enter
(`Certify2426.isContLocalMartingaleBefore_congr`, module `InteractingSLE.Spec.Sec2.T2426Cert`). -/
def IsContLocalMartingaleBefore {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) (ζ : Ω → WithTop ℝ≥0) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ContinuousOn (fun t => X t ω) {t | (t : WithTop ℝ≥0) < ζ ω}) ∧
    ∃ σ : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime 𝓕 (σ n)) ∧ (∀ n ω, σ n ω = 0 ∨ σ n ω < ζ ω) ∧
      (∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < ζ ω → ∀ᶠ n in atTop, (r : WithTop ℝ≥0) < σ n ω) ∧
      ∀ n, Martingale (stoppedProcess (fun t => {ω | 0 < σ n ω}.indicator (X t)) (σ n)) 𝓕 P

end InteractingSLE
