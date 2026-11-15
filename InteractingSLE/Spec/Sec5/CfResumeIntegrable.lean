/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfResumeErase

/-!
# Integrable pairings of the random record image field

Packet PROVE-CFCHART2, continuation. Convert the fixed-time chart clause to the image
field's stopping-time clause and apply the existing bounded random-word mean theorem.
This discharges the integrability requirement of `CfGivenChartStatement` at every prefix time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CfResume

open CfGiven CfConv Exist Exist.Staged Exist.StagedLaw Restart Restart.DomainMarkov
open Sec7.PocketTraversal

section Chart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {R : Ω → RecData}
  {𝓐 : Filtration ℝ≥0 mΩ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ}

/-- The stopping-time coupling clause for the image field, extracted from the same
transport used in `hasSafeLaw_imgField_of_chartConst`. -/
theorem isCouplingCharFun_imgField_of_chartConst (hκ : 0 < κ) (hh : Measurable h)
    (h𝒢 : MeasurableSpace.comap R inferInstance ≤ 𝓐 0)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hchart : Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 W
      (geomLW W xL) (geomRW W xR) (fun _ => ⊤) (fun ω => cfChart (R ω))
      (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω)) :
    Coupling.MartMeans.IsCouplingCharFun (16 / κ) ρL ρR P (usualAugmentation 𝓐 P) W
      (geomLW W xL) (geomRW W xR) (fun _ => ⊤) (fun ω => imgField κ (R ω) (h ω)) := by
  have hhn : Measurable fun ω => -h ω :=
    LQGMetric.measurable_distOn_iff.2 fun φ => ((LQGMetric.measurable_distOn_apply φ).comp hh).neg
  have hc := fun ω => isConformal_cfChart (R ω)
  have hlift := fun ω => continuousOn_lift_cfChart (R ω)
  have hU := Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation hhn hc hlift
    (fun ω => (hWc ω).continuousOn) (fun i ω => (isForcePath_geomLW hWc xL ω i).1.continuousOn)
    (fun j ω => (isForcePath_geomRW hWc xR ω j).1.continuousOn)
    (fun ω t _ => ⟨fun i => geomLW_le hWc xL ω t i, fun j => le_geomRW hWc xR ω t j⟩) hchart
  have hR0 : Measurable[usualAugmentation 𝓐 P 0] R :=
    (Measurable.of_comap_le h𝒢).mono (Ito.le_usualAugmentation 𝓐 P 0) le_rfl
  exact Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hc
    (fun z => hR0 (measurableSet_mem_dom_cfChart z))
    (fun z => (measurable_indicator_fwd_cfChart z).comp hR0)
    (fun z => (measurable_indicator_lift_cfChart z).comp hR0) hlift hhn
    (ae_of_all _ fun ω => ⟨hW0 ω, (hWc ω).continuousOn⟩) hU
    (fun ω => isChartTransport_cfChart_imgField hκ (R ω) (h ω))

/-- The bounded mean theorem for a random initial word discharges image-field
integrability directly from the converted chart clause. -/
theorem integrable_imgField_of_chartConst (hκ : 0 < κ) (hh : Measurable h)
    (h𝒢 : MeasurableSpace.comap R inferInstance ≤ 𝓐 0)
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous fun t => W t ω)
    (hchart : Sec7.Lemma71D.IsChartCouplingCharFunConst (16 / κ) ρL ρR P 𝓐 W
      (geomLW W xL) (geomRW W xR) (fun _ => ⊤) (fun ω => cfChart (R ω))
      (-(π * chiC κ)) (-chiC κ) (fun ω => -h ω)) (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => imgField κ (R ω) (h ω) φ) P := by
  have hRm : Measurable R := (Measurable.of_comap_le h𝒢).mono (𝓐.le 0) le_rfl
  have hXm := (measurable_imgField κ).comp (hRm.prodMk hh)
  exact WangWu.integrable_apply_of_isCouplingCharFun_of_bounded
    (isCouplingCharFun_imgField_of_chartConst hκ hh h𝒢 hW0 hWc hchart)
    (ae_of_all _ fun ω => ⟨ENNReal.coe_lt_top, (hWc ω).continuousOn, hW0 ω⟩) φ
    ((LQGMetric.measurable_distOn_apply φ).comp hXm)

end Chart

/-- The exact image-field integrability requirement at every prefix time, with the
same source inputs as the positive-time chart construction. -/
theorem integrable_imgField_recOf_of_strip {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hA : PartAInputsSixteenDivOfClearance)
    (href : Sec7.Lemma71H.Cond44ReferenceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b J)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hleft : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, y < 0 → y ∉ J →
      b y + a * chiC κ ≤ -sleLambda κ)
    (hright : ∀ a ∈ Icc (-(π / 2)) (π / 2), ∀ y : ℝ, 0 < y → y ∉ J →
      sleLambda κ ≤ b y + a * chiC κ)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) {D : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hDm : Measurable D) (hDreg : ∀ ω, IsRegularDriver (D ω))
    (hD : IsFlowLineDriver κ b J θ P h (fun t ω => (D ω).1 t) (fun ω => (D ω).2))
    (s : ℝ≥0) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) ⊤ (η ω))
    (φ : TestOn upperHalfPlaneOpens) :
    Integrable (fun ω => imgField κ (recOf (s : ℝ≥0∞) (D ω)) (h ω) φ) P := by
  by_cases hs : s = 0
  · subst s
    exact integrable_imgField_recOf_zero hcf D φ
  · have hs0 : 0 < s := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ s) (Ne.symm hs)
    obtain ⟨𝓐, V, η', h𝒢, _, _, _, _, _, _, hV0, hVc, _, _, hchart, _⟩ :=
      exists_chartConst_omega hA href hκ hκ4 hb hcf hζ' hleft hright hθ hDm hDreg hD hs0 hη
    exact integrable_imgField_of_chartConst hκ hh h𝒢 hV0 hVc hchart φ

end InteractingSLE.Sec5.CfResume
