/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvReduce

/-!
# Conditional completion after the exact chart conversion

Packet PROVE-CFCHART2. This conditional helper records the remaining mathematical inputs
explicitly: integrable pairings of the random chart field, a flow-line classification of the
reduced word, and the member identities in the retained filtration. It does not discharge
these inputs or assert `CfGivenChartStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CfConv

open CfGiven Exist.StagedLaw Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7.PocketTraversal

/-- Once the three remaining mathematical inputs hold for the converted data, the
conditional counterflow law follows in the actual record kernel. -/
theorem ae_isCenteredCounterflowDriver_of_converted_chart {Ω : Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) {R : Ω → RecData} (hR : Measurable R) {𝓐 : Filtration ℝ≥0 mΩ}
    (h𝒢 : MeasurableSpace.comap R inferInstance ≤ 𝓐 0) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : Measurable[MeasurableSpace.comap R inferInstance] xL)
    (hxR : Measurable[MeasurableSpace.comap R inferInstance] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j)
    (hxLa : ∀ ω, Antitone (xL ω)) (hxRm : ∀ ω, Monotone (xR ω))
    {V : ℝ≥0 → Ω → ℝ} (hV0 : ∀ ω, V 0 ω = 0) (hVc : ∀ ω, Continuous fun t => V t ω)
    (hVa : StronglyAdapted 𝓐 V) (hthr : ∀ᵐ ω ∂P, FCDet.thr ρL ρR V xL xR ω = ⊤)
    (hchart : Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 V
      (geomLW V xL) (geomRW V xR) (fun _ => ⊤) (fun ω => cfChart (R ω))
      (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω))
    (hintegrable : ∀ φ : TestOn upperHalfPlaneOpens,
      Integrable (fun ω => imgField κ (R ω) (h ω) φ) P)
    (hword : ∀ᵐ ω ∂P, ∃ c : BoundaryWord, FCDet.IsFlowType (16 / κ) 0 c (xL ω) (xR ω) ρL ρR)
    (hlocal : HasSafeMembers P 𝓐 univ (fun _ => ⊤) V (fun ω => imgField κ (R ω) (h ω))) :
    ∀ᵐ ω₀ ∂P, IsCenteredCounterflowDriver κ (condExpKernel P (MeasurableSpace.comap R inferInstance) ω₀)
      (fun ω => recField κ (R ω₀) (h ω)) V (fun _ => ⊤) :=
  ae_isCenteredCounterflowDriver_of_hasSafeLaw hκ hh hR h𝒢 hxL hxR hxL0 hxR0 hxLa hxRm hV0 hVc hVa
    hintegrable hthr hword (hasSafeLaw_imgField_of_chartConst hκ hh h𝒢 hV0 hVc hchart) hlocal

end InteractingSLE.Sec5.CfConv
