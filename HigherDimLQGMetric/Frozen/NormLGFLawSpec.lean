-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLQGMetric.Frozen.NormLGFLaw
import HigherDimLQGMetric.Assembly.NormLGFLawSpec

/-!
# Frozen theorem: `normLGFLaw_spec`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 50–57 (the whole-space LGF; `h_1(0) = 0`), l. 1573 (`𝔞_ε` is defined from the law of the
normalized LGF). Sanity anchor (MA0 fidelity note 4–5, "existence of a normalized LGF"): for `d ≥ 2`,
`normLGFLaw d` is a probability measure, it is the law of a normalized LGF (so whole-space LGFs exist and
the axioms' quantifiers over LGF-plus-continuous inputs are not vacuous), and it is the only such law (so
the `Classical.choose` in `normLGFLaw` and the normalization `𝔞_ε` are canonical).

State `DRAFT_SORRY` (ruling M13): the body is exactly `by sorry` until it is sealed as
`by exact HigherDimLQGMetric.normLGFLaw_spec_impl` (provider `HigherDimLQGMetric.Assembly.NormLGFLawSpec`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- Sanity anchor: the normalized LGF exists and its law `normLGFLaw d` is unique. -/
theorem normLGFLaw_spec :
    ∀ (d : ℕ), 2 ≤ d → IsProbabilityMeasure (normLGFLaw d) ∧ IsNormalizedLGF id (normLGFLaw d) ∧
      ∀ μ : Measure (DistRd d), IsProbabilityMeasure μ → IsNormalizedLGF id μ → μ = normLGFLaw d :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLQGMetric.normLGFLaw_spec_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLQGMetric
-- FROZEN_ANCHOR_SUFFIX_END
