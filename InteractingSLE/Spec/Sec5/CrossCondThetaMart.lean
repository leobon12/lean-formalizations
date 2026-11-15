/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondThetaIdent

/-!
# The cross-conditioning law at relative angle `θ`: the image word's martingale clause

Packet PROVE-CROSSCOND-THETA. G4 at a general relative angle `θ`: on the glued space of the flow line of `h` and the
counterflow of `h − θχ` (`CrossCondTheta`), the explicit coupling means of the killed image word (the flow line read in
the counterflow chart `Ψ`, stopped at its first contact with the counterflow hull) with the junction weights `cLT θ`,
`cRT θ` are local martingales in the image word's filtration.

* **`imageWordFiltThetaStatement θ : ImageWordFiltThetaStatement θ`** — PROVED for every `θ` (under the setting's
  hypotheses, among them `CfThetaBounds κ θ`), from the mean identification `meanIdentThetaStatement` through the
  θ-versions of PROVE-GLUECOND7's steps: the chart clause at fixed image times (R1–R6:
  `ae_condExp_cfGlue_eq_cfFT`, `ae_condExp_imgRaw_eq_cfFT`, `imgChartConstThetaStatement_of_ident_marks`), the marks
  (`imgMarksThetaStatement`) and step B4 (`imageWordFiltThetaStatement_of_chartConst`);
* `exists_isWordEntrance_of_filtTheta`: the word entrance (Lemma 2.11) from the martingale clause;
* at `θ = π/2` this is the landed `Word49.ImageWord49FiltCStatement` (`imageWord49FiltCStatement_of_theta`; the junction
  weights `cLT (π/2) = cL6`, `cRT (π/2) = cR6` of ruling R57).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CrossCond.Theta

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets Word49
open ImgDrv MartChar Sec7.PhaseSelFull Sec7.Aux117
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyIdx dyF dyIdx_eq_iff setIntegral_eq_of_dyadic ae_condExp_eq_of_forall_setIntegral)

/-! ### The statements and the martingale clause from the chart clause -/

section Defs

/-- θ-version of `ImageWord49FiltWStatement` (`Sec5.CrossCondMart`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
def ImageWordFiltThetaStatement (θ : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR → CfThetaBounds κ θ ρL ρR xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ s : ℝ≥0, 0 < s → ∀ z ∈ H,
          IsLocalMartingaleBefore
            (imgFilt (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) xL xR s ζ W
              (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W))
            (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))
            (fun p => min (QuantumZipper.swallowTime (wpath (imgW s ζ W
                (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ
                    W))
                p) z : WithTop ℝ≥0)
              (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p))
            (coupProc κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
              (imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W))
              (imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W))
              (imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W)) z)

/-- θ-version of `ImgChartConst49Statement` (`Sec5.CrossCondMart`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
def ImgChartConstThetaStatement (θ : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR → CfThetaBounds κ θ ρL ρR xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ s : ℝ≥0, 0 < s →
          Sec7.Lemma71D.IsChartCouplingCharFunConst κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
            (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))
            (imgRaw xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W))
            (imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W))
            (imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W))
            (imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W))
            (fun p => (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p : ℝ≥0∞))
            (fun p => cfChart s p.2) (2 * Real.pi * chiC κ) (chiC κ) (fun p => h p.1)

/-- θ-version of `imageWord49FiltWStatement_of_chartConst` (`Sec5.CrossCondMart`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem imageWordFiltThetaStatement_of_chartConst {θ : ℝ} (hI : ImgChartConstThetaStatement.{u} θ) :
    ImageWordFiltThetaStatement.{u} θ := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 hθb Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
    z hz
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49T θ s hs κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
      hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  obtain ⟨hnull, hK, hWa, hVLa, hVRa, hσ, hσm, hσT, hσlim, hζq⟩ :=
    filtClauses (μ := μ) (xL := xL) (xR := xR) hWad hF hae
  set 𝓖 := imgFilt μ xL xR s ζ W E with h𝓖
  have : 𝓖.IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  set ζ' : Ω × HistorySpace 0 0 → ℝ≥0∞ := fun p => (imgT s ζ W E p : ℝ≥0∞) with hζ'
  set hF' : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => h p.1 with hFdef
  have hFm : Measurable hF' := hC.2.1.comp measurable_fst
  have hcc : ∀ p : Ω × HistorySpace 0 0, (cfChart s p.2).IsConformal := fun p => isConformal_cfChart p.2
  have hlc : ∀ p : Ω × HistorySpace 0 0, ContinuousOn (cfChart s p.2).2.2 (cfChart s p.2).dom := fun p =>
    continuousOn_lift_cfChart p.2
  -- the chart clause at every stopping time of `imgFilt`
  have hcf0 := hI κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  have hcfU : Coupling.MartMeans2.IsChartCouplingCharFun κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) μ 𝓖 (imgW s ζ W E)
      (imgVL xL s ζ W E) (imgVR xR s ζ W E) ζ' (fun p => cfChart s p.2) (2 * Real.pi * chiC κ) (chiC κ) hF' :=
    Sec7.Lemma71D.isChartCouplingCharFun_usualAugmentation hFm hcc hlc (fun p => hK.contW p)
      (fun i p => (hK.pathL p i).1) (fun j p => (hK.pathR p j).1)
      (fun p t ht => ⟨fun i => hK.ordL p t i ht, fun j => hK.ordR p t j ht⟩) hcf0
  -- the transported field
  set h' : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens :=
    fun p => Sec7.Lemma71K.chartField (cfChart s p.2) (2 * Real.pi * chiC κ) (chiC κ) (hF' p) with hh'
  have ht : ∀ p, IsChartTransport (cfChart s p.2) 1 (2 * Real.pi * chiC κ) (chiC κ) (hF' p) (h' p) := fun p =>
    Sec7.Lemma71K.isChartTransport_chartField (hcc p) (hlc p) _ _ (hF' p)
  have hY : Measurable[𝓖 0] fun p : Ω × HistorySpace 0 0 => cfStop s p.2 := measurable_cfStop_imgFilt 0
  have hdom : ∀ z, MeasurableSet[𝓖 0] {p : Ω × HistorySpace 0 0 | z ∈ (cfChart s p.2).dom} := fun z =>
    measurableSet_mem_dom_cfChart_comp (Y := Prod.snd) hY z
  have hfwd : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 0 0 | z ∈ (cfChart s p.2).dom}.indicator fun p => (cfChart s p.2).1 z) := fun z =>
    measurable_indicator_fwd_cfChart_comp (Y := Prod.snd) hY z
  have hliftm : ∀ z, Measurable[𝓖 0]
      ({p : Ω × HistorySpace 0 0 | z ∈ (cfChart s p.2).dom}.indicator fun p => (cfChart s p.2).2.2 z) := fun z =>
    measurable_indicator_lift_cfChart_comp (Y := Prod.snd) hY z
  have hcf' : Coupling.MartMeans.IsCouplingCharFun κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) μ 𝓖 (imgW s ζ W E)
      (imgVL xL s ζ W E) (imgVR xR s ζ W E) ζ' h' :=
    Coupling.MartMeans2.isCouplingCharFun_of_isChartTransport hcc hdom hfwd hliftm hlc hFm
      (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p⟩) hcfU ht
  -- measurability of the transported field
  have hh'm : Measurable h' := by
    have hm := Chart.measurable_chartTransport_random' hcc (fun z => 𝓖.le 0 _ (hdom z))
      (fun z => (hfwd z).mono (𝓖.le 0) le_rfl) (fun z => (hliftm z).mono (𝓖.le 0) le_rfl) hlc hFm 1
      (2 * Real.pi * chiC κ) (chiC κ)
    have e : h' = fun p => Chart.chartTransport (hcc p) 1 (2 * Real.pi * chiC κ) (chiC κ) (hF' p) := by
      funext p
      simp only [hh', Sec7.Lemma71K.chartField, hcc p, ↓reduceDIte]
    rw [e]
    exact hm
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun p => h' p φ) μ := fun φ =>
    integrable_apply_of_isCouplingCharFun_of_bounded hcf'
      (Eventually.of_forall fun p => ⟨(isKilledArc_gCurve hEg p).zero_lt_kLife, hK.contW p, hK.w_zero p⟩)
      φ ((LQGMetric.measurable_distOn_apply φ).comp hh'm)
  -- the filtration clauses
  have hζm : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {p | ζ' p ≤ t} := by
    intro t
    have h1 := (hζq t).compl
    convert h1 using 1
    ext p
    simp only [hζ', mem_ofPred_eq, mem_compl_iff, not_lt]
    rfl
  have hT : Coupling.IsAnnouncingSeq 𝓖 μ ζ' (imgAnn s ζ W E) :=
    ⟨hσ, hσm, fun n => Eventually.of_forall fun p => hσT n p, hσlim⟩
  obtain ⟨G, hG, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull
    (MartChar.adaptedBefore_of_stronglyAdapted hζm hWa)
    (fun i => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVLa i))
    (fun j => MartChar.adaptedBefore_of_stronglyAdapted hζm (hVRa j))
    (Eventually.of_forall fun p => ⟨hK.w_zero p, hK.contW p, ⟨fun i => (hK.pathL p i).1, fun j => (hK.pathR p j).1⟩,
      fun t ht => ⟨fun i => hK.ordL p t i ht, fun j => hK.ordR p t j ht⟩⟩)
    hT hint hcf' (fun p t => meanExt κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) (imgW s ζ W E t p)
      (fun i => imgVL xL s ζ W E i t p) (fun j => imgVR xR s ζ W E j t p))
    (fun p t => isBoundedHarmonicExtension_meanExt κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) _ _ _) hz
  exact Restart.ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG hGae
    (Restart.ConverseBefore.measurable_coupProc_zero hK.w_zero (fun i => measurable_imgVL xL hWad hE hEg i 0)
      (fun j => measurable_imgVR xR hWad hE hEg j 0) hz) hloc

/-- θ-version of `exists_isWordEntrance_of_filtW` (`Sec5.CrossCondMart`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem exists_isWordEntrance_of_filtTheta {θ : ℝ} (hI : ImageWordFiltThetaStatement.{u} θ) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (Bi : ℝ≥0 → (Ω × HistorySpace 0 0) × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration
        (imgFilt (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) xL xR s ζ W
          (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W)) 𝓦)
        Bi ((glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)).prod P₀) ∧
      (∀ p, Continuous fun t => Bi t p) ∧
      ∀ᵐ p ∂((glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)).prod P₀),
        IsWordEntrance κ
          (fun i => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) i 0 p.1)
          (fun j => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) j 0 p.1)
          (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
          (fun t => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) t p.1)
          (fun i t => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) i t p.1)
          (fun j t => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) j t p.1)
          (fun t => Bi t p)
          (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p.1 : ℝ≥0∞) := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  have hW : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49T θ s hs κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
      hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  obtain ⟨hnull, hK, hWa, hVLa, hVRa, hσ, hσm, hσT, hσlim, -⟩ := filtClauses (xL := xL) (xR := xR) hW hF hae
  exact hK.exists_isWordEntrance hκ hnull hWa hVLa hVRa hσ hσm hσT hσlim
    (hI κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

/-- θ-version of `ImgMarks49Statement` (`Sec5.CrossCondMartPass`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
def ImgMarksThetaStatement (θ : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR → CfThetaBounds κ θ ρL ρR xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ s : ℝ≥0, 0 < s →
          (∀ (r : ℝ≥0) (t' t : ℚ), (0 : ℝ) ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 0 0),
            MeasurableSet[imgRaw xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) r] A →
            ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧
              B' =ᵐ[glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)]
                A ∩ {p | (t' : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                    ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p ∧
                  (r : ℝ) < capClock (gCurve s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                    ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p) t'}) ∧
          ∀ t : ℚ, 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
            ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧
              B' =ᵐ[glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)]
                cfAv s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                  ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) φ (t : ℝ).toNNReal

end Defs

/-! ### The chart clause from the mean identification (R1–R6) -/

section R1

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- θ-version of `ae_condExp_cfGlue_eq_cfF` (`Sec5.CrossCondMartFwd`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem ae_condExp_cfGlue_eq_cfFT (hMI : MeanIdentThetaStatement.{u} θ) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {s : ℝ≥0} (hs : 0 < s) {t : ℝ≥0} (ht : 0 < t) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ cfAv s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) φ t →
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 0 0 => hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)
            (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔ cfGlueMarks W VL VR ζ t s] p =
        cfF (cLT θ) (cRT θ) κ ρL ρR xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) φ
          (capClock (gCurve s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p) t).toNNReal p := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  set U : Ω × HistorySpace 0 0 → Set ℂ := fun p => hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2
    with hUdef
  set F : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)) with hFdef
  have hX := hC.2.2.2.1
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hFg := isZeroBoundaryGFF_cenTT_glue (θ := θ) (k := k) hC hu₀
  have hAm : Measurable[_, hittingSigma] U :=
    measurable_union_hitting (((measurable_hullAt t).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ s).comp measurable_snd)
  have hAae := ae_hullAt_eq_image_seedLine hκ hκ4 hF h44 hC
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hAae] with ω hω using hω.1
  have hreg₂ := ae_cfRegT hκ hθb hC hcf hlaw
  have hmark := isHistoryAvoidanceLocal_cfGlueT hC hκ hζ hcf hreg₂ hlaw hk hu₀ t s
  have hℋ := cfGlueMarks_le (Ω := Ω) t s hX
  obtain ⟨M, -, hM1, hM2⟩ := exists_condExp_germSigma_history hFg hAm hℋ hmark
    (Eventually.of_forall fun p => union_relClosed t s _ p.2) φ
  -- the constant `e^{i ∫ 𝔥₀ φ}` is pulled out
  set c : ℂ := Complex.exp (Complex.I * ((∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have e : (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) =
      c • fun p => Complex.exp (Complex.I * (F p φ : ℂ)) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, hc, hFdef, cenTT_cfFieldT, ← Complex.exp_add]
    rw [show h p.1 - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ =
      centredField h u₀ p.1 from rfl, centredField_apply h hu₀.1 p.1 φ]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ := μ) c (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (F p φ : ℂ)))
    (germSigma U F ⊔ cfGlueMarks W VL VR ζ t s)
  rw [← e] at hpull
  have hid := hMI κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk u₀ hu₀ s hs t ht φ
  filter_upwards [hM1, hM2, hpull, hid, ae_glue_fst (μ := P) k hXm hAae] with p h1 h2 h5 h4 hAp hAv
  obtain ⟨hpE, htP, hav⟩ := hAv
  have hset := cfChart_inv_image_eq hEg hpE htP (hAp.2 t)
  rw [h5, Pi.smul_apply, ← h2, smul_eq_mul]
  have hMp : M p = Sec7.Lemma71D.chartMean κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) (fun r => imgW s ζ W E r p)
      (fun i r => imgVL xL s ζ W E i r p) (fun j r => imgVR xR s ζ W E j r p) (cfChart s p.2)
      (2 * Real.pi * chiC κ) (chiC κ) φ (capClock (gCurve s ζ W E p) t).toNNReal - ∫ z, u₀ z * φ z := by
    rw [h1, ← h4 ⟨hpE, htP, hav⟩]
    ring
  have hv : QuantumZipper.zeroGFFTestCov (H \ relClosureH (U p)) φ φ =
      Sec7.Lemma71D.chartVar (fun r => imgW s ζ W E r p) (cfChart s p.2) φ
        (capClock (gCurve s ζ W E p) t).toNNReal := by
    obtain ⟨hsub, hopen⟩ := union_relClosed t s (killedHistory W VL VR ζ p.1) p.2
    rw [Sec7.Lemma71D.chartVar, hset, relClosureH_eq hsub hopen]
  rw [hv, hMp, cfF, hc, ← mul_assoc, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- θ-version of `ae_condExp_imgRaw_eq_cfF` (`Sec5.CrossCondMartPass`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem ae_condExp_imgRaw_eq_cfFT (hMI : MeanIdentThetaStatement.{u} θ) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR)
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s)
    (hM1 : ∀ (r : ℝ≥0) (t' t : ℚ), (0 : ℝ) ≤ t' → t' ≤ t → 0 < t → ∀ A : Set (Ω × HistorySpace 0 0),
      MeasurableSet[imgRaw xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) r] A →
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)]
          A ∩ {p | (t' : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p ∧
            (r : ℝ) < capClock (gCurve s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p) t'})
    (hM3 : ∀ t : ℚ, 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
      ∃ B', MeasurableSet[cfGlueMarks W VL VR ζ (t : ℝ).toNNReal s] B' ∧
        B' =ᵐ[glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)]
          cfAv s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) φ (t : ℝ).toNNReal)
    (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) t p)
        (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p : ℝ≥0∞) (cfChart s p.2) φ r →
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          imgRaw xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) r] p =
        cfF (cLT θ) (cRT θ) κ ρL ρR xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
          ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) φ r p := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hX := hC.2.2.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49T θ s hs κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
      hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  have hEae : ∀ᵐ p ∂μ, p ∈ E := ae_mem_glueGood hae
  obtain ⟨u₀, hu₀⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR xL xR
  have hFg := isZeroBoundaryGFF_cenTT_glue (θ := θ) (k := k) hC hu₀
  have hXm : Measurable fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (((LQGMetric.measurable_distOn_apply φ).comp hC.2.1).comp measurable_fst)))
  have hXb : ∀ p : Ω × HistorySpace 0 0, ‖Complex.exp (Complex.I * (h p.1 φ : ℂ))‖ ≤ 1 := fun p => by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hXi : Integrable (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (h p.1 φ : ℂ))) μ :=
    Integrable.of_bound hXm.aestronglyMeasurable 1 (Eventually.of_forall hXb)
  obtain ⟨hErm, hmeanm, hvarm⟩ := measurable_cfChartAvoid_raw (xL := xL) (xR := xR) (cLT θ) (cRT θ) κ ρL ρR hF hWad hE
      hEg r φ
  set Er := {p : Ω × HistorySpace 0 0 | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
    (imgT s ζ W E p : ℝ≥0∞) (cfChart s p.2) φ r} with hErdef
  -- the candidate is `imgRaw r`-measurable on `Er`
  have hGm : Measurable[imgRaw xL xR s ζ W E r] (Er.indicator (cfF (cLT θ) (cRT θ) κ ρL ρR xL xR s ζ W E φ r)) := by
    have e : Er.indicator (cfF (cLT θ) (cRT θ) κ ρL ρR xL xR s ζ W E φ r) = Er.indicator (fun p => Complex.exp
        (Complex.I *
        ((Er.indicator (fun p => Sec7.Lemma71D.chartMean κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) (fun t => imgW s ζ W
            E t p)
          (fun i t => imgVL xL s ζ W E i t p) (fun j t => imgVR xR s ζ W E j t p) (cfChart s p.2)
          (2 * Real.pi * chiC κ) (chiC κ) φ r) p : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * Er.indicator (fun p => Sec7.Lemma71D.chartVar (fun t => imgW s ζ W E t p)
          (cfChart s p.2) φ r) p : ℝ) : ℂ))) := by
      refine Set.indicator_congr fun p hp => ?_
      simp only [cfF, indicator_of_mem hp]
    rw [e]
    refine Measurable.indicator ?_ hErm
    exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hmeanm).const_mul _ |>.sub
      (Complex.measurable_ofReal.comp (hvarm.const_mul _)))
  have hGi : Integrable (Er.indicator (cfF (cLT θ) (cRT θ) κ ρL ρR xL xR s ζ W E φ r)) μ := by
    refine Integrable.of_bound ((hGm.mono ((imgRaw xL xR s ζ W E).le r) le_rfl).aestronglyMeasurable) 1
      (Eventually.of_forall fun p => ?_)
    by_cases hp : p ∈ Er
    · rw [indicator_of_mem hp]
      exact norm_cfF_le_one hF hEg φ hp.1
    · rw [indicator_of_notMem hp, norm_zero]
      exact zero_le_one
  refine ae_condExp_eq_of_forall_setIntegral ((imgRaw xL xR s ζ W E).le r) hErm hXi hGm.stronglyMeasurable hGi ?_
  intro A hA
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hUm : ∀ t : ℝ≥0, Measurable[_, hittingSigma] fun p : Ω × HistorySpace 0 0 =>
      hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2 := fun t =>
    measurable_union_hitting (((measurable_hullAt t).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ s).comp measurable_snd)
  refine setIntegral_eq_of_dyadic hXi (Eventually.of_forall hXb)
    (fun n j => germSigma (fun p : Ω × HistorySpace 0 0 =>
      hullAt (dyq n j) (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)
        (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔ cfGlueMarks W VL VR ζ (dyq n j) s)
    (fun n j => sup_le (germSigma_le (hUm _) hFg.measurable) (cfGlueMarks_le _ _ hX))
    (Av := cfAv s ζ W E φ)
    (F := fun q p => cfF (cLT θ) (cRT θ) κ ρL ρR xL xR s ζ W E φ (capClock (gCurve s ζ W E p) q).toNNReal p)
    (fun q p hp => norm_cfF_le_one hF hEg φ hp.2.2.1) ?_ (measurable_cfTheta hWad hE hEg r)
    (((imgRaw xL xR s ζ W E).le r _ hA).inter ((imgRaw xL xR s ζ W E).le r _ hErm)) ?_ ?_
  · -- the clause at the dyadic forward times
    intro n j
    exact ae_condExp_cfGlue_eq_cfFT hMI hκ hκ4 hF h44 hθb hC hcf hlaw k hk hu₀ hs (dyq_pos' n j) φ
  · -- the pieces are in the marks
    intro n j
    have ht0 := dyqR_pos n j
    obtain ⟨B1, hB1m, hB1e⟩ := hM1 r (dyqR n j) (dyqR n j) (by exact_mod_cast ht0.le) le_rfl ht0 (A ∩ Er)
      (hA.inter hErm)
    obtain ⟨B2, hB2m, hB2e⟩ := hM1 r ((j : ℚ) / 2 ^ n) (dyqR n j) (by push_cast; positivity) (divR_le_dyqR n j) ht0
      univ MeasurableSet.univ
    obtain ⟨B3, hB3m, hB3e⟩ := hM3 (dyqR n j) ht0 φ
    rw [dyqR_toNNReal] at hB1m hB2m hB3m hB3e
    rw [dyqR_coe] at hB1e
    rw [divR_coe] at hB2e
    refine ⟨B1 ∩ B2ᶜ ∩ B3, le_sup_right (a := germSigma (fun p : Ω × HistorySpace 0 0 =>
      hullAt (dyq n j) (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)
        (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)))) _ ((hB1m.inter hB2m.compl).inter hB3m), ?_⟩
    refine ((hB1e.inter hB2e.compl).inter hB3e).trans ?_
    refine Eventually.of_forall fun p => ?_
    simp only [mem_inter_iff, mem_compl_iff, mem_univ, true_and, eq_iff_iff]
    constructor
    · rintro ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
      have hh := (dyIdx_cfTheta_and_mem_cfAv_iff hEg hEr.1 n j φ).2 ⟨h1, h2, h3⟩
      exact ⟨⟨⟨hAp, hEr⟩, hh.1⟩, hh.2⟩
    · rintro ⟨⟨⟨hAp, hEr⟩, hd⟩, hav⟩
      obtain ⟨h1, h2, h3⟩ := (dyIdx_cfTheta_and_mem_cfAv_iff hEg hEr.1 n j φ).1 ⟨hd, hav⟩
      exact ⟨⟨⟨⟨hAp, hEr⟩, h1⟩, h2⟩, h3⟩
  · -- the right limit
    filter_upwards [hEae] with p hpE hpD
    exact tendsto_cfF_dyF hF hEg hpE hpD.2

/-- θ-version of `imgChartConst49Statement_of_ident_marks` (`Sec5.CrossCondMartPass`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem imgChartConstThetaStatement_of_ident_marks (hMI : MeanIdentThetaStatement.{u} θ)
    (hM : ImgMarksThetaStatement.{u} θ) : ImgChartConstThetaStatement.{u} θ := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 hθb Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  obtain ⟨hM1, hM3⟩ := hM κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  have hEg : ∀ p ∈ glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s
      ζ W,
      IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hkw := isKilledWord_img (ζ := ζ) (W := W) (xL := xL) (xR := xR) hF hEg
  intro r u hu φ
  filter_upwards [ae_condExp_imgRaw_eq_cfFT hMI hκ hκ4 hF h44 hθb hC hcf hlaw k hk hs hM1 hM3 r φ] with p hp hr hsupp
  have hav : Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W (glueGood (glueMeasure P k
      (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) t p)
      (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))
        s ζ W) p : ℝ≥0∞) (cfChart s p.2) φ r := ⟨hr, hsupp⟩
  rw [hp hav, cfF]
  have hint := Sec7.Lemma71D.integral_couplingMean_eq_chartMean (κ := κ) (ρL := jwL (cLT θ) κ ρL) (ρR := jwR (cRT θ) κ
      ρR)
    (a := 2 * Real.pi * chiC κ) (k := chiC κ) (isConformal_cfChart p.2) (hkw.contW p) hav
    (fun i => hkw.ordL p r i hr) (fun j => hkw.ordR p r j hr) (hu p)
  congr 3
  exact congrArg Complex.ofReal hint.symm

end R1

/-! ### The marks -/

section Marks

/-- θ-version of `imgMarks49Statement` (`Sec5.CrossCondMartMarks`):
the counterflow field is `h − θχ` instead of `h − π/2 χ`. -/
theorem imgMarksThetaStatement (θ : ℝ) : ImgMarksThetaStatement.{u} θ := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 hθb Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  have hEg : ∀ p ∈ glueGood μ s ζ W, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49T θ s hs κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
      hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := (ae_hullAt_eq_image_seedLine hκ hκ4 hF h44 hC).mono fun ω hω => hω.1
  have hXm : Measurable fun ω => cfFieldT κ θ (h ω) := (measurable_cfFieldT κ θ).comp hC.2.1
  have hgood : ∀ᵐ p ∂μ, p ∈ glueGood μ s ζ W ∧ Aux50Hit.IsGoodPath W VL VR ζ p.1 := by
    filter_upwards [ae_mem_glueGood hae, ae_glue_fst (μ := P) k hXm (Aux50Hit.ae_isGoodPath hC.1 hζ)]
      with p h1 h2
    exact ⟨h1, h2⟩
  refine ⟨fun r t' t ht'0 ht't ht A hA => ?_, fun t ht φ => ?_⟩
  · exact exists_marks_ae_eq_inter xL xR ht hEg hgood r ht'0 ht't hA
  · exact exists_marks_ae_eq_avoid ht hEg hgood φ

end Marks

/-! ### The image word's martingale clause at relative angle `θ` -/

section Main

/-- **The chart clause at fixed image times from the mean identification** (relative angle `θ`). -/
theorem imgChartConstThetaStatement_of_ident {θ : ℝ} (hMI : MeanIdentThetaStatement.{u} θ) :
    ImgChartConstThetaStatement.{u} θ :=
  imgChartConstThetaStatement_of_ident_marks hMI (imgMarksThetaStatement θ)

/-- **The image word's martingale clause at relative angle `θ` from the mean identification.** -/
theorem imageWordFiltThetaStatement_of_ident {θ : ℝ} (hMI : MeanIdentThetaStatement.{u} θ) :
    ImageWordFiltThetaStatement.{u} θ :=
  imageWordFiltThetaStatement_of_chartConst (imgChartConstThetaStatement_of_ident hMI)

/-- **G4 at relative angle `θ`: the image word's martingale clause** (junction weights `cLT θ`, `cRT θ`), proved for
every `θ` from `meanIdentThetaStatement`. -/
theorem imageWordFiltThetaStatement (θ : ℝ) : ImageWordFiltThetaStatement.{u} θ :=
  imageWordFiltThetaStatement_of_ident (meanIdentThetaStatement θ)

/-- **At `θ = π/2` the martingale clause is the landed `ImageWord49FiltCStatement`** (R57's weights). -/
theorem imageWord49FiltCStatement_of_theta (hT : ImageWordFiltThetaStatement.{u} (π / 2)) :
    ImageWord49FiltCStatement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44
  rw [← cLT_pi_div_two, ← cRT_pi_div_two]
  exact hT κ hκ hκ4 xL xR ρL ρR hF h44 (cfThetaBounds_of_cond44 hκ hκ4 hF h44)

/-- The landed `imageWord49FiltCStatement` re-derived from the general-angle theorem. -/
theorem imageWord49FiltCStatement' : ImageWord49FiltCStatement.{u} :=
  imageWord49FiltCStatement_of_theta (imageWordFiltThetaStatement (π / 2))

end Main

end InteractingSLE.Sec5.CrossCond.Theta
