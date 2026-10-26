-- FROZEN_ANCHOR_PREFIX_BEGIN
import HigherDimLFPPAS.Frozen.IsAdmissibleSeed
import HigherDimLQGMetric.Frozen.ConvMollify
import HigherDimLQGMetric.Frozen.IsNormalizedLGF
import HigherDimLFPPAS.Implementation.ConvMollifyJointSeed

/-!
# Frozen theorem: `convMollify_joint_seed`

Anchor of the statement surface of the HigherDimLFPPAS formalization (manifest
`HigherDimLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, L7, L8; statement audit
`planning/audits/S1-statement-audit.md`, §5.3 and condition C3).
Source: `source/higher-dimensional-lfpp-almost-sure.pdf` ([AS], sha256 `7476d6f4…da93197`, cited by line of the
text extraction `source/higher-dimensional-lfpp-almost-sure.txt`): l. 71 ("`h*_ε = h ∗ K_ε`"), l. 125 (the limit
along all positive `ε`), Appendix A, l. 784–787 (radial representation of `h ∗ K_ε`) and l. 854–857 ("a jointly
differentiable version [...] We choose this version").
Characterization anchor of the sealed `HigherDimLQGMetric.convMollify` on the signed carrier, simultaneously
in the cutoff: for the normalized LGF, almost surely, for every `ε > 0` and every `z`
the truncated pairings defining `h * K_ε` converge, and `(ε, z) ↦ h*_ε(z)` is continuous on `(0, ∞) × ℝ^d`.
This pins the meaning of `lfppDist κ ξ ε (h ω)` for all `ε` on one probability-one event (the version lemma of
the statement audit, §5.2).

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact HigherDimLFPPAS.Implementation.convMollify_joint_seed_impl`, provider
`HigherDimLFPPAS.Implementation.ConvMollifyJointSeed`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLFPPAS

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem convMollify_joint_seed :
    ∀ (d : ℕ), 2 ≤ d → ∀ κ : Rd d → ℝ, IsAdmissibleSeed κ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ᵐ ω ∂P,
          (∀ ε : ℝ, 0 < ε → ∀ z : Rd d,
            Tendsto (fun n : ℕ => h ω (convTrunc κ ε z n)) atTop (𝓝 (convMollify κ ε (h ω) z))) ∧
          ContinuousOn (fun p : ℝ × Rd d => convMollify κ p.1 (h ω) p.2) (Ioi 0 ×ˢ univ) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact HigherDimLFPPAS.Implementation.convMollify_joint_seed_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end HigherDimLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
