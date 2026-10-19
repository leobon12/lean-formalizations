-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPP.Frozen.Kappa
import LQGDimension.Statement.Defs
import HigherDimLFPP.TwoD.GFFCorollary

/-!
# Frozen theorem: `gff_circle_average_lfpp`

Anchor of the statement surface of the higher-dimensional LFPP formalization (manifest
`HigherDimLFPP/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`).
Source: `source/higher-dimensional-lfpp-limit.pdf`, §1.1, Lemma A.1 and the planar convention of [5] (the 2D paper; `LQGDimension`).
Ruling H9 (i): `LQGDimension.theorem11_lambda` without its existence hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

/-- **d = 2, whole-plane GFF.** For circle-average LFPP of the whole-plane GFF normalized by
`h₁(0) = 0` (the setting of `LQGDimension`), the LFPP exponent exists for all small `ξ > 0`, and
`λ(ξ)/ξ^{4/3} → κ₂` as `ξ ↓ 0`. -/
theorem gff_circle_average_lfpp :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (h : ℝ → ℂ → Ω → ℝ),
      LQGDimension.IsGFFCircleAverage h P →
      (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, ∃ lam : ℝ, LQGDimension.IsLFPPExponent h P ξ lam) ∧
      ∀ lam : ℝ → ℝ, (∃ ξ₀ > 0, ∀ ξ ∈ Ioo (0 : ℝ) ξ₀, LQGDimension.IsLFPPExponent h P ξ (lam ξ)) →
        Tendsto (fun ξ => lam ξ / ξ ^ (4 / 3 : ℝ)) (𝓝[>] 0) (𝓝 (kappa 2)) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPP.gff_circle_average_lfpp_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPP
-- FROZEN_ANCHOR_SUFFIX_END
