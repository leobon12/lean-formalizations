-- FROZEN_ANCHOR_PREFIX_BEGIN
import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing
import SupercriticalLQGUniqueness.Frozen.IsLFPPNormalizer
import SupercriticalLQGUniqueness.Frozen.RescaledLFPP
import SupercriticalLQGUniqueness.Frozen.LSCMetricToLSCFun
import SupercriticalLQGUniqueness.Frozen.LSCTendsto
import SupercriticalLQGUniqueness.Frozen.LSCTendstoInProbability
import SupercriticalConformalCovariance.Frozen.XiCrit
import SupercriticalLFPPAS.Implementation.Lfpp_ae_lscTendsto

/-!
# Frozen theorem: `lfpp_ae_lscTendsto`

Anchor of the statement surface of the SupercriticalLFPPAS formalization (manifest
`SupercriticalLFPPAS/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, P6 and P7; independent statement
audit `planning/audits/S1-statement-audit.md`, verdict PASS with NOTE, notes N1–N5).
Source: `source/almost-sure-supercritical-lfpp.pdf` (sha256 `98dd7695…af229c9f`, cited by line of the text
extraction `source/almost-sure-supercritical-lfpp.txt`): Theorem 1.1, l. 34–42, with the conventions of l. 21–32
((1.1), the median normalizer `𝔞_ε`, the limit `D_h` of [1, Theorems 1.3 and 1.8]) and the meaning of the topology,
l. 44–51 ((1.2) and recovery, on one probability-one event, infinite distances allowed).

Ruling P6: the heat versions `X ε` are required to be almost surely jointly continuous in `(ε, z)`, which selects the
paper's realization-wise convolution `h ∗ p_{ε²/2}` (l. 25, l. 164). Without this hypothesis the statement is false
(the refuted version v1, `SupercriticalLFPPAS.RefutedV1.not_thm11v1`). Such families exist (`exists_jointHeatVersion`,
`SupercriticalLFPPAS/Frozen/Exists_jointHeatVersion.lean`) and any two agree almost surely at every `ε` at once
(`SupercriticalLFPPAS.ae_eq_of_jointHeatVersions`). Ruling P7 approved this text (S1 condition C1: the statement
surface v2, `planning/drafts/S0Surface-v2.lean.txt`, frozen byte for byte). Theorem 1.1 counts as proved only when
this anchor and `exists_jointHeatVersion` are both sealed (condition C3).

Proof body: the region between the `FROZEN_ANCHOR_PROOF` markers. Its state is recorded by the manifest:
`DRAFT_SORRY` (body exactly `by sorry`) or `SEALED` (body exactly
`by exact SupercriticalLFPPAS.Implementation.lfpp_ae_lscTendsto_impl`, provider
`SupercriticalLFPPAS.Implementation.Lfpp_ae_lscTendsto`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric (DistC)

namespace SupercriticalLFPPAS

open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF IsHeatSmoothing IsLFPPNormalizer
  rescaledLFPP LSCMetric LSCTendsto LSCTendstoInProbability)
open SupercriticalConformalCovariance (xiCrit)

/-- **Almost sure convergence of supercritical LFPP** (paper Theorem 1.1, l. 34–42 of
`source/almost-sure-supercritical-lfpp.txt`, with the conventions of l. 21–32). Fix `ξ > ξ_crit`
(`xiCrit`, DG (1.7)). Let `𝔞_ε` be the median of the left–right crossing distance of `[0,1]²`
(`IsLFPPNormalizer`, unique by the sealed `existsUnique_isLFPPNormalizer`), `h` a whole-plane GFF
normalized by `h_1(0) = 0`, `X ε` a continuous version of `h*_ε = h * p_{ε²/2}` (`IsHeatSmoothing`),
and `L` the limit in probability of `𝔞_ε⁻¹ D^ε_h` in the topology on lower semicontinuous functions
of DG Definition 1.2 (`D_h` of [1, Theorems 1.3 and 1.8]: it exists by the sealed
`lfpp_tendstoInProbability` and is almost surely unique). Then, on one probability-one event of the
space carrying `h`, for every sequence of positive `ε_n → 0` the functions `𝔞_{ε_n}⁻¹ D^{ε_n}_h`
converge to `D_h` in the sense of DG Definition 1.2 (`LSCTendsto`): the lower-limit property (1.2)
and the recovery property (l. 44–51); values `∞` are allowed. -/
theorem lfpp_ae_lscTendsto :
    ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) →
      ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
          (∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2) →
        ∀ L : Ω → LSCMetric,
          LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
            (fun ω => (L ω).toLSCFun.1) →
          ∀ᵐ ω ∂P, ∀ ε : ℕ → Set.Ioi (0 : ℝ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
            LSCTendsto (fun n => rescaledLFPP (ξ : ℝ) (m (ε n)) (X (ε n) ω)) (L ω).toLSCFun.1 :=
-- FROZEN_ANCHOR_PROOF_BEGIN
  by exact SupercriticalLFPPAS.Implementation.lfpp_ae_lscTendsto_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN

end SupercriticalLFPPAS
-- FROZEN_ANCHOR_SUFFIX_END
