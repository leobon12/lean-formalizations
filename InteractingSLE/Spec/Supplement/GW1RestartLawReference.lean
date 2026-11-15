/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1RestartLaw
import InteractingSLE.Spec.Sec5.CrossCondThetaMart

/-!
# The field-law clause of the relative-angle reference comparison

The all-angle cross-conditioning mean identifies the field law at every optional
time of the image exploration. This extracts the full characteristic-functional
clause used inside `imageWordFiltThetaStatement_of_chartConst`, with the literal
inherited offset `2πχ`. Its `(4.4)` and `CfThetaBounds` premises remain visible.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1RestartLaw

open Sec4 Sec5 Sec5.CrossCond Sec5.CrossCond.Theta Sec5.CrossCond.Word49
open WangWu WangWu.ImgWord LawUnique Sec5.GlueCond Sec5.CfRegQ Sec5.Prop411Q
open WangWu.ImgDrv Sec5.Cond44Ref MartChar Sec7.PhaseSelFull Sec7.Aux117

/-- The actual field in the counterflow-history chart, with its inherited phase. -/
def referenceField {Ω : Type u} (κ : ℝ) (s : ℝ≥0)
    (h : Ω → DistOn upperHalfPlaneOpens) (p : Ω × HistorySpace 0 0) :
    DistOn upperHalfPlaneOpens :=
  Sec7.Lemma71K.chartField (cfChart s p.2) (2 * Real.pi * chiC κ) (chiC κ) (h p.1)

/-- Under the reference assumptions the image word has the full optional field
characteristic functional, not only the driving martingale clause. -/
theorem reference_isCouplingCharFun {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂)
    (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    {s : ℝ≥0} (hs : 0 < s) :
    let μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
      ((measurable_cfFieldT κ θ).comp hC.2.1)
    let E := glueGood μ s ζ W
    Coupling.MartMeans.IsCouplingCharFun κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
      μ (imgFilt μ xL xR s ζ W E) (imgW s ζ W E)
      (imgVL xL s ζ W E) (imgVR xR s ζ W E)
      (fun p => (imgT s ζ W E p : ℝ≥0∞)) (referenceField κ s h) := by
  let μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
    ((measurable_cfFieldT κ θ).comp hC.2.1)
  let E := glueGood μ s ζ W
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49T θ s hs κ hκ hκ4 xL xR ρL ρR hF h44 hθb
      P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  obtain ⟨-, hK, -, -, -, -, -, -, -, -⟩ :=
    filtClauses (μ := μ) (xL := xL) (xR := xR) hC.1.2.1 hF hae
  let 𝓖 := imgFilt μ xL xR s ζ W E
  have hcc : ∀ p : Ω × HistorySpace 0 0, (cfChart s p.2).IsConformal :=
    fun p => isConformal_cfChart p.2
  have hlc : ∀ p : Ω × HistorySpace 0 0,
      ContinuousOn (cfChart s p.2).2.2 (cfChart s p.2).dom :=
    fun p => continuousOn_lift_cfChart p.2
  have hc0 := imgChartConstThetaStatement_of_ident (meanIdentThetaStatement θ)
    κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC
    P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  have hU := Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation
    (hC.2.1.comp measurable_fst) hcc hlc
    (fun p => hK.contW p) (fun i p => (hK.pathL p i).1)
    (fun j p => (hK.pathR p j).1)
    (fun p t ht => ⟨fun i => hK.ordL p t i ht, fun j => hK.ordR p t j ht⟩) hc0
  have hY : Measurable[𝓖 0] fun p : Ω × HistorySpace 0 0 => cfStop s p.2 :=
    measurable_cfStop_imgFilt 0
  have hdom : ∀ z, MeasurableSet[𝓖 0]
      {p : Ω × HistorySpace 0 0 | z ∈ (cfChart s p.2).dom} :=
    fun z => measurableSet_mem_dom_cfChart_comp (Y := Prod.snd) hY z
  have hfwd : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 0 0 | z ∈ (cfChart s p.2).dom}.indicator
        fun p => (cfChart s p.2).1 z) :=
    fun z => measurable_indicator_fwd_cfChart_comp (Y := Prod.snd) hY z
  have hlift : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 0 0 | z ∈ (cfChart s p.2).dom}.indicator
        fun p => (cfChart s p.2).2.2 z) :=
    fun z => measurable_indicator_lift_cfChart_comp (Y := Prod.snd) hY z
  exact Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hcc hdom hfwd hlift hlc
    (hC.2.1.comp measurable_fst) (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p⟩)
    hU (fun p => Sec7.Lemma71K.isChartTransport_chartField (hcc p) (hlc p) _ _ (h p.1))

end InteractingSLE.Theorem14.GW1RestartLaw
