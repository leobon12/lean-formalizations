-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.DistExp
import HigherDimLQGMetric.Assembly.DistExpSpec

/-!
# Frozen theorem: `distExp_spec`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M7, M9, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 50, 92–93; [1] (1.7) and its footnote; [2] Proposition 1.1; rulings M7, M9 (D-KI replaces [6]).
Sanity anchor (MA0 fidelity note 4): `distExp` is not junk. For `d ≥ 2` and `ξ > 0`, the exponent exists
for every admissible kernel and is kernel independent (`IsDistanceExponent d ξ (distExp d ξ)`), and it is
unique (the choice in `distExp` is canonical).

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.distExp_spec_impl` (provider `HigherDimLQGMetric.Assembly.DistExpSpec`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section


namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Sanity anchor: `distExp d ξ` is the unique kernel-independent LFPP distance exponent `Q(ξ)`. -/
theorem distExp_spec :
    ∀ (d : ℕ), 2 ≤ d → ∀ ξ : ℝ, 0 < ξ → ∀ Q : ℝ, IsDistanceExponent d ξ Q ↔ Q = distExp d ξ :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.distExp_spec_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
