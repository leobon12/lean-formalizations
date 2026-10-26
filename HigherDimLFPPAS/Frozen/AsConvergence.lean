-- FROZEN_ANCHOR_PREFIX_BEGIN
import Mathlib
import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLFPPAS.Frozen.Assumption11
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import Mathlib.Topology.Instances.ENNReal.Lemmas
import HigherDimLFPPAS.Implementation.AsConvergence

/-!
# Frozen theorem: `asConvergence`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L6, L7, L8; statement audit
`planning/audits/S1-statement-audit.md`).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): **Theorem 1.2**, l. 118–125, with the setting of
§1: `d ≥ 3`, `ξ > 0` (l. 49), the normalized whole-space LGF `h` (l. 49–55), the seed `κ` of (1.2) (l. 57–71),
`D^ε` (1.3), `𝔞_ε` (1.4), and Assumption 1.1 (l. 90–116). Conclusion (1.7): almost surely, for every compact
`F ⊂ ℝ^d`, `sup_{x, y ∈ F} |𝔞_ε⁻¹ D^ε_h(x, y) − D_h(x, y)| → 0` along all `ε ↓ 0` (l. 125), the supremum computed
in `[0, ∞]` (`edist` on `ℝ`, complete-lattice `⨆`: no junk value). The faithful main theorem: signed seeds
(ruling L7), Assumption 1.1 read by ruling L6.

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLFPPAS.Implementation.asConvergence_impl`, provider `HigherDimLFPPAS.Implementation.AsConvergence`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HigherDimLFPPAS

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- **Theorem 1.2.** For `d ≥ 3`, `ξ > 0`, an admissible seed `κ`, and an assignment `D` satisfying
Assumption 1.1 for the normalized LGF `h`: almost surely, for every compact `F`,
`sup_{x, y ∈ F} |𝔞_ε⁻¹ D^ε_h(x, y) − D_h(x, y)| → 0` as `ε ↓ 0`. -/
theorem asConvergence :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ →
    ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
    ∀ D : DistRd d → ContMetric d,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d),
      IsNormalizedLGF h P → Assumption11 d ξ κ D P h →
      ∀ᵐ ω ∂P, ∀ F : Set (Rd d), IsCompact F →
        Tendsto (fun ε : ℝ => ⨆ p ∈ F ×ˢ F,
            edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p))
          (𝓝[>] 0) (𝓝 0) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPPAS.Implementation.asConvergence_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
