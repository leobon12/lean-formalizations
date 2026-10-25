import SupercriticalLQGUniqueness.Frozen.RescaledLFPP

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `LSCTendstoInProbability`. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- Convergence in probability as `ε → 0` with respect to the topology on lower semicontinuous
functions of DG Definition 1.2 (DG l. 326), in subsequence form: for every sequence of positive
`ε_n → 0` there is a subsequence along which, almost surely, `F ε ω` converges to `L ω` in the
sense of DG Definition 1.2 (`LSCTendsto`, l. 314–317). For a topology induced by a metric (DG
l. 321–322) this is equivalent to convergence in probability for that metric (ruling F30-R5). -/
def LSCTendstoInProbability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Set.Ioi (0 : ℝ) → Ω → ℂ × ℂ → EReal) (L : Ω → ℂ × ℂ → EReal) : Prop :=
  ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, LSCTendsto (fun k => F (ε (φ k)) ω) (L ω)

end SupercriticalLQGUniqueness
