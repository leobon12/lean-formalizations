import SupercriticalLQGUniqueness.Frozen.IsNormalizedWholePlaneGFF
import SupercriticalLQGUniqueness.Frozen.IsHeatSmoothing
import SupercriticalLQGUniqueness.Frozen.IsLFPPNormalizer
import SupercriticalLQGUniqueness.Frozen.RescaledLFPP
import SupercriticalLQGUniqueness.Frozen.LSCMetricToLSCFun
import SupercriticalLQGUniqueness.Frozen.LSCTendsto
import SupercriticalLQGUniqueness.Frozen.LSCTendstoInProbability
import SupercriticalConformalCovariance.Frozen.XiCrit
import SupercriticalLFPPAS.Assembly.Adapters
import SupercriticalLFPPAS.Local.Interface
import SupercriticalLFPPAS.Field.InterfaceForms
import SupercriticalLFPPAS.Normalizer.Window

/-!
# Provider of the frozen anchor `lfpp_ae_lscTendsto` (paper Theorem 1.1)

`lfpp_ae_lscTendsto_impl` restates the exact type of `SupercriticalLFPPAS.lfpp_ae_lscTendsto`
(`SupercriticalLFPPAS/Frozen/Lfpp_ae_lscTendsto.lean`; rulings P6, P7; statement surface v2, S1 condition C1), with the
anchor's imports first and the same `open`s, and proves it. This module never imports the anchor.

Proof: the assembly `Assembly.lfpp_ae_lscTendsto_of_window` (`SupercriticalLFPPAS/Assembly/Adapters.lean`, packet ASM)
composes all landed packets (§§2–7 of the corrected rewrite in `blueprint/`) into the anchor's type
`Core.Lfpp_ae_lscTendstoStmt`, with Lemma 6.1 (the corrected symmetric normalizer window `Core.NormalizerWindowStmt S`)
as its only input. Lemma 6.1 is `Normalizer.normalizerWindow_of` (packet L61), applied for every setup `S` (ξ, the
exponent `Q`, the median normalizer `𝔞`, the strong LQG metric `D`) to the confinement Lemma 2.2
(`Local.confinement_of`, from the localized comparison (2.7)–(2.8) `Assembly.locCompare_holds` and the localized
approximation (2.1) `Field.locApprox_holds`) and to the mesh oscillation bound (2.2) `Field.meshOsc_holds`. No
hypothesis beyond the anchor's binders remains.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open LQGMetric (DistC)

namespace SupercriticalLFPPAS.Implementation

open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF IsHeatSmoothing IsLFPPNormalizer
  rescaledLFPP LSCMetric LSCTendsto LSCTendstoInProbability)
open SupercriticalConformalCovariance (xiCrit)

/-- **Almost sure convergence of supercritical LFPP** (paper Theorem 1.1): the exact type of the frozen anchor
`SupercriticalLFPPAS.lfpp_ae_lscTendsto`, proved by the assembly `Assembly.lfpp_ae_lscTendsto_of_window` with
Lemma 6.1 from `Normalizer.normalizerWindow_of`. -/
theorem lfpp_ae_lscTendsto_impl :
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
  Assembly.lfpp_ae_lscTendsto_of_window fun S : Core.Setup =>
    Normalizer.normalizerWindow_of S
      (Local.confinement_of S (Assembly.locCompare_holds S) Field.locApprox_holds)
      Field.meshOsc_holds

end SupercriticalLFPPAS.Implementation
