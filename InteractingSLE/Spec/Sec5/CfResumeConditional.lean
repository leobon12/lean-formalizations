/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfResumeIntegrable

/-!
# Conditional counterflow after erasure, with integrability discharged

Packet PROVE-CFCHART2, continuation. The remaining mathematical hypotheses are exactly
the reduced word's flow type and the member identities. Integrability follows from the
chart clause. This conditional helper is distinct from `CfGivenChartStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfResume

open CfGiven CfConv Exist.StagedLaw Restart Restart.DomainMarkov.K2 Sec7.PocketTraversal

/-- The converted raw chart gives the conditional counterflow after ordered erasure
of zero weights. Locality and the reduced-word classification remain explicit; image-field
integrability, threshold preservation and all reindexing requirements are proved. -/
theorem ae_counterflow_of_erased_chart {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {nL nR kL kR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (eL : Fin kL ↪o Fin nL) (eR : Fin kR ↪o Fin nR)
    (heL : ∀ j, j ∉ range eL → ρL j = 0) (heR : ∀ j, j ∉ range eR → ρR j = 0)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {R : Ω → RecData} (hR : Measurable R) {𝓐 : Filtration ℝ≥0 mΩ}
    (h𝒢 : MeasurableSpace.comap R inferInstance ≤ 𝓐 0)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : Measurable[MeasurableSpace.comap R inferInstance] xL)
    (hxR : Measurable[MeasurableSpace.comap R inferInstance] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω))
    {V : ℝ≥0 → Ω → ℝ} (hV0 : ∀ ω, V 0 ω = 0)
    (hVc : ∀ ω, Continuous fun t => V t ω) (hVa : StronglyAdapted 𝓐 V)
    (hthr : ∀ᵐ ω ∂P, FCDet.thr ρL ρR V xL xR ω = ⊤)
    (hchart : Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 V
      (geomLW V xL) (geomRW V xR) (fun _ => ⊤) (fun ω => cfChart (R ω))
      (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω))
    (hword : ∀ᵐ ω ∂P, ∃ c : BoundaryWord,
      FCDet.IsFlowType (16 / κ) 0 c (xL ω ∘ eL) (xR ω ∘ eR) (ρL ∘ eL) (ρR ∘ eR))
    (hlocal : HasSafeMembers P 𝓐 univ (fun _ => ⊤) V
      (fun ω => imgField κ (R ω) (h ω))) :
    ∀ᵐ ω₀ ∂P,
      IsCenteredCounterflowDriver κ (condExpKernel P (MeasurableSpace.comap R inferInstance) ω₀)
        (fun ω => recField κ (R ω₀) (h ω)) V (fun _ => ⊤) := by
  have hthr' : ∀ᵐ ω ∂P,
      FCDet.thr (ρL ∘ eL) (ρR ∘ eR) V (fun ω => xL ω ∘ eL) (fun ω => xR ω ∘ eR) ω = ⊤ := by
    filter_upwards [hthr] with ω hω
    exact (thr_reindex_zero eL.toEmbedding eR.toEmbedding ρL ρR heL heR V xL xR ω).trans hω
  have hchart' := chartConst_reindex_zero eL.toEmbedding eR.toEmbedding heL heR
    (fun ω => isConformal_cfChart (R ω)) hVc hchart
  have hxL' : Measurable[MeasurableSpace.comap R inferInstance] (fun ω => xL ω ∘ eL) := by
    let : MeasurableSpace Ω := MeasurableSpace.comap R inferInstance
    exact measurable_pi_iff.2 fun i => (measurable_pi_apply (eL i)).comp hxL
  have hxR' : Measurable[MeasurableSpace.comap R inferInstance] (fun ω => xR ω ∘ eR) := by
    let : MeasurableSpace Ω := MeasurableSpace.comap R inferInstance
    exact measurable_pi_iff.2 fun j => (measurable_pi_apply (eR j)).comp hxR
  exact ae_isCenteredCounterflowDriver_of_converted_chart hκ hh hR h𝒢
    hxL' hxR'
    (fun ω i => hxL0 ω (eL i)) (fun ω j => hxR0 ω (eR j))
    (fun ω _ _ hij => hxLa ω (eL.monotone hij)) (fun ω _ _ hij => hxRm ω (eR.monotone hij))
    hV0 hVc hVa hthr' hchart'
    (integrable_imgField_of_chartConst hκ hh h𝒢 hV0 hVc hchart) hword hlocal

end InteractingSLE.Sec5.CfResume
