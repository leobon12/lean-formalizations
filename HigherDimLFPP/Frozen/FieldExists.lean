-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPP.Frozen.IsLFPPKernel
import HigherDimLFPP.Frozen.IsBandVersion
import HigherDimLFPP.Field.Exists

/-!
# Frozen theorem: `field_exists`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1 (non-vacuity of the hypotheses of `theorem11`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- Non-vacuity: admissible kernels exist in every dimension `d ≥ 1`, and for each of them there is
a probability space with a white noise `W` and continuous versions `H ε` of `H_{ε,1}`. -/
theorem field_exists : ∀ d : ℕ, 1 ≤ d →
    (∃ κ : Rd d → ℝ, IsLFPPKernel κ) ∧
    ∀ κ : Rd d → ℝ, IsLFPPKernel κ →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : WN d → Ω → ℝ)
        (H : ℝ → Rd d → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsWhiteNoise P W ∧
          ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPP.field_exists_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPP
-- FROZEN_ANCHOR_SUFFIX_END
