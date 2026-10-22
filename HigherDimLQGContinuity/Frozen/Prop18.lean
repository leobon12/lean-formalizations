-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGContinuity.Frozen.XiRange
import HigherDimLQGMetric.Frozen.DistExp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import HigherDimLQGContinuity.Assembly.Prop18

/-!
# Frozen theorem: `prop18`

Anchor of the statement surface of the HigherDimLQGContinuity formalization (manifest
`HigherDimLQGContinuity/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, N1, N3, N4).
Source: `source/higher-dimensional-lqg-continuity.pdf` ([C], sha256 `05368f93…2f9c2e5934`, cited by line of the
text extraction `source/higher-dimensional-lqg-continuity.txt`): (1.5) and l. 74–81 ("The map `γ ↦ ξ` is a
continuous increasing bijection of the subcritical intervals, and `γ/ξ → d` at zero [3, Proposition 1.8 and
Corollary 1.9]"), l. 121 (`ϕ(0) = 1`), l. 1309 ("the parameter homeomorphism (1.5)"). Ruling N3: [3] is not
formalized (its exponent is a different object, NA1 S-1); the statement is about the repository's exponent
`Q = HigherDimLQGMetric.distExp d` and follows from NA1's R1 (`ϕ = ξQ` is `√(2d)`-Lipschitz on `[0, ∞)` with
`ϕ(0) = 1`). Content: `Q` is continuous on `(0, ∞)` and strictly decreasing on the subcritical set
`{ξ > 0 : √(2d) < Q(ξ)}`; `ϕ(ξ) = ξQ(ξ) → 1` as `ξ ↓ 0`; and there is an increasing homeomorphism `Ξ` of
`[0, √(2d))` onto `xiRange d = [0, ξ_c)` (`ξ_c = sup xiRange d ∈ (0, ∞]`) with `Ξ 0 = 0`, such that for
`0 < γ < √(2d)` the parameters `ξ > 0` with `Q(ξ) = d/γ + γ/2` are exactly `ξ = Ξ γ`, and `γ / Ξ γ → d` as
`γ ↓ 0`. Parametrization and non-vacuity anchor of `theorem11` (closure condition C1, ruling N4). Not asserted
(not used by [C]): finiteness of `ξ_c`, and monotonicity of `d_γ = γ/ξ` ([3] Proposition 1.8, second half).

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly `by exact HigherDimLQGContinuity.prop18_impl`,
provider `HigherDimLQGContinuity.Assembly.Prop18`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- **The parametrization (1.5)** ([C] l. 74–81; [3, Prop. 1.8, Cor. 1.9] for the repository's exponent).
`Q = distExp d` is continuous on `(0, ∞)`, strictly decreasing on the subcritical set, `ξ Q(ξ) → 1` at `0⁺`,
and `γ ↦ ξ` is an increasing homeomorphism `Ξ` of `[0, √(2d))` onto `xiRange d`, characterized by
`Q(ξ) = d/γ + γ/2`, with `γ / Ξ γ → d` at `0⁺`. -/
theorem prop18 :
    ∀ d : ℕ, 3 ≤ d →
      ContinuousOn (distExp d) (Ioi 0) ∧
      StrictAntiOn (distExp d) {ξ : ℝ | 0 < ξ ∧ Real.sqrt (2 * d) < distExp d ξ} ∧
      Tendsto (fun ξ => ξ * distExp d ξ) (𝓝[>] 0) (𝓝 1) ∧
      ∃ Ξ : ℝ → ℝ, Ξ 0 = 0 ∧
        StrictMonoOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        ContinuousOn Ξ (Ico 0 (Real.sqrt (2 * d))) ∧
        Ξ '' Ico 0 (Real.sqrt (2 * d)) = xiRange d ∧
        (∀ γ ∈ Ioo (0 : ℝ) (Real.sqrt (2 * d)), ∀ ξ : ℝ, 0 < ξ →
          (distExp d ξ = (d : ℝ) / γ + γ / 2 ↔ ξ = Ξ γ)) ∧
        Tendsto (fun γ => γ / Ξ γ) (𝓝[>] 0) (𝓝 (d : ℝ)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGContinuity.prop18_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGContinuity
-- FROZEN_ANCHOR_SUFFIX_END
