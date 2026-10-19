-- FROZEN_ANCHOR_PREFIX_BEGIN
import GaussianLQG.Frozen.QConst
import GaussianLQG.Frozen.IsCanonicalLQGMetric
import GaussianLQG.Assembly.MainUnconditional
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Frozen theorem: the main theorem

Keystone anchor (manifest `GaussianLQG/Frozen/frozen-anchors.json`): source Theorem 1.1, blueprint
v3 Theorem `thm:main`, with no trust input. Its hypotheses are: `D γ` is the canonical γ-LQG metric for
`γ ∈ (0,2)` (ruling R3), and `h` is a whole-plane GFF normalized by `h_1(0) = 0` on any probability
space. Conclusions: `q` is the unique median of `M`, and `q < 0`; `(D^γ(0,1) - 1)/γ → (H(0,0) - q)/2`
in probability; the limit has law `N(-q/2, 3/8)`; convergence in law; and every median `m_γ` of
`D^γ(0,1)` satisfies `m_γ = 1 - (q/2) γ + o(γ)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace GaussianLQG

/-- **Main theorem** (source Theorem 1.1, blueprint Theorem `thm:main`).

Anchor `main_theorem_v2`: the same statement as `main_theorem_v1`, with all binders after the colon so
that the sealed body can be the bare assembly `by exact <provider>` required by the frozen-anchor
checker. The elaborated types agree (checked in both directions by application). -/
theorem main_theorem :
    ∀ (D : ℝ → LQGMetric.DistC → LQGMetric.ContMetric)
    (_hD : ∀ γ, 0 < γ → γ < 2 → IsCanonicalLQGMetric γ (D γ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → LQGMetric.DistC) (_hh : LQGMetric.IsNormalizedWPGFF h P),
    -- `q` is the unique median of `M`, and `q < 0`
    (LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) qConst ∧
      ∀ m, LQGMetric.IsMedian (P.map fun ω => diagMin (h ω)) m → m = qConst) ∧
    qConst < 0 ∧
    -- (1.7): convergence in probability
    TendstoInMeasure P (fun γ ω => ((D γ (h ω)).1 (0, 1) - 1) / γ) (𝓝[>] 0)
      (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) ∧
    -- the limit has law `N(-q/2, 3/8)`
    P.map (fun ω => (segPairing (h ω) 0 0 - qConst) / 2) =
      gaussianReal (-qConst / 2) (3 / 8 : NNReal) ∧
    -- (1.8): convergence in law to `N(-q/2, 3/8)` (indexed by `γ ∈ (0,2)`)
    TendstoInDistribution (fun (γ : Ioo (0 : ℝ) 2) ω => ((D γ (h ω)).1 (0, 1) - 1) / (γ : ℝ))
      ((𝓝[>] (0 : ℝ)).comap Subtype.val) (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal (-qConst / 2) (3 / 8 : NNReal)) ∧
    -- (1.9) for every choice of medians `m_γ` of `D^γ(0,1)`
    ∀ m : ℝ → ℝ, (∀ γ, 0 < γ → γ < 2 →
        LQGMetric.IsMedian (P.map fun ω => (D γ (h ω)).1 (0, 1)) (m γ)) →
      Tendsto (fun γ => (m γ - (1 - qConst / 2 * γ)) / γ) (𝓝[>] 0) (𝓝 0) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact GaussianLQG.main_theorem_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end GaussianLQG
-- FROZEN_ANCHOR_SUFFIX_END
