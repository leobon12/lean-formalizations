import GaussianLQG.Core.Defs
import GaussianLQG.LQG.Bridge.Defs
import GaussianLQG.Frozen.QConst
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Objects of the main theorem

The definitions used in the statement of the main theorem (blueprint Theorem `thm:main`) are frozen
in `GaussianLQG/Frozen/` (one declaration per file; manifest `GaussianLQG/Frozen/frozen-anchors.json`); this file
re-exports them and keeps the internal input proposition `UniformMomentInput` ((S6), source Lemma 2.1),
which Phase B proves for the canonical metric.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

-- `segPairing`, `dyadicUnit`, `diagMin` and `qConst` (blueprint Definition `def:HMq`) are the frozen
-- definitions in `GaussianLQG/Frozen/{SegPairing,DyadicUnit,DiagMin,QConst}.lean`.

/-- Input (S6): uniform moments of the `1/2`-Hölder constant and of inverse separated distances
(source Lemma 2.1), under the law of the normalized whole-plane GFF.

This is **not proved** anywhere. It is the source's own Lemma 2.1, whose proof (source Appendix A)
is a reduction to an unproved uniform-in-ξ version of DDDF20 Lemma A.1 (blueprint erratum E16,
audit A4). The main theorem takes it as a hypothesis under ruling R7. -/
def UniformMomentInput (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric) : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∃ γp : ℝ, 0 < γp ∧ ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ γ ∈ Ioc (0 : ℝ) γp,
      (∫⁻ g, holderConst (D γ g).1 K ^ p ∂LQGMetric.normGFFLaw) ≤ C ∧
      (∫⁻ g, (sepInf (D γ g).1 K δ)⁻¹ ^ p ∂LQGMetric.normGFFLaw) ≤ C

end GaussianLQG
