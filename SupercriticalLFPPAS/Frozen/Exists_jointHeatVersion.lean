-- FROZEN_ANCHOR_PREFIX_BEGIN
import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing
import SupercriticalLFPPAS.Implementation.Exists_jointHeatVersion

/-!
# Frozen theorem: `exists_jointHeatVersion`

Anchor of the statement surface of the SupercriticalLFPPAS formalization (manifest
`SupercriticalLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, P6 and P7; independent statement
audit `planning/audits/S1-statement-audit.md` §5, verdict PASS).
Source: `source/almost-sure-supercritical-lfpp.pdf` (sha256 `98dd7695…af229c9f`, cited by line of the text
extraction `source/almost-sure-supercritical-lfpp.txt`): l. 21–25 and (1.1), `h*_ε = h ∗ p_{ε²/2}` for every
`ε > 0` as one realization-wise family (differentiated in the cutoff at l. 164). Non-vacuity anchor of the
joint-continuity hypothesis of `lfpp_ae_lscTendsto` (ruling P6; S1 condition C2: frozen exactly as S1 §5.1).

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact SupercriticalLFPPAS.Implementation.exists_jointHeatVersion_impl`, provider
`SupercriticalLFPPAS.Implementation.Exists_jointHeatVersion`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric (DistC)

namespace SupercriticalLFPPAS

open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF IsHeatSmoothing)

/-- **Jointly continuous heat versions exist** (non-vacuity of the version hypothesis of
`lfpp_ae_lscTendsto`, ruling P6; paper l. 21–25, (1.1): `h*_ε = h * p_{ε²/2}` for all `ε > 0`).
For every whole-plane GFF `h` normalized by `h_1(0) = 0` on a probability space there is a family
`X ε` of continuous versions of `h*_ε` (`IsHeatSmoothing`, one for each `ε > 0`) such that,
almost surely, `(ε, z) ↦ X ε ω z` is jointly continuous on `(0, ∞) × ℂ`. -/
theorem exists_jointHeatVersion :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
        ∃ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) ∧
          ∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact SupercriticalLFPPAS.Implementation.exists_jointHeatVersion_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end SupercriticalLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
