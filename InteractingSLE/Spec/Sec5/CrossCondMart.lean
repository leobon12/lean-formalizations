/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondArg
import InteractingSLE.WangWu.ReverseContactMartFilt2

/-!
# The martingale clause of the image word from the chart clause at fixed image times (general `κ`)

Packet PROVE-GLUECOND7. The general-`κ` form of WangWu's step B4 (`imageWordFiltStatement_of_chartConst`,
PROVE-WW-B18): PROVE-GLUECOND5 reduced G4 in Proposition 4.9's direction to the named martingale clause
`Word49.ImageWord49FiltStatement` (the explicit coupling means of the killed image word are local martingales in the
filtration `imgFilt` of the image word). This file derives it from the **chart coupling clause at fixed image times of
the raw filtration** `imgRaw`, written through the counterflow chart `cfChart s y = (Ψ, Ψ⁻¹, Im L_Ψ)` with the
coordinate rule (1.4) at lift coefficient `χ` and height shift `2πχ` (`Im L_Ψ → −2π` on the physical real line, where
`Ψ′ > 0`; see `CrossCondArg`):

`h = (𝔥_r ∘ Ψ − 2πχ − χ Im L_Ψ) + (zero-boundary GFF on Ψ⁻¹(ℍ ∖ K̃_r))` given `imgRaw r`, on `{r < imgT}`,

with `𝔥_r` the coupling mean of the image word (weights `jwL cL κ ρL`, `jwR cR κ ρR`). The clause is lifted to every
stopping time of `imgFilt` (`Lemma71D.isChartCouplingCharFun_usualAugmentation`), transported to the half-plane
through the chart (`MartMeans2.isCouplingCharFun_of_isChartTransport`), and turned into local martingales of the
explicit coupling means (`MartMeans2.exists_isLocalMartingaleBefore_meanProcOn`,
`ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn`); the pairings of the transported field are integrable
(`WangWu.integrable_apply_of_isCouplingCharFun_of_bounded`).

## Main results

* `measurable_comp_of_stopSigma`: a function measurable for the stopped-history σ-algebra, read through a map whose
  stopped history is measurable, is measurable;
* the chart is known at time `0` of the raw and of the augmented filtration (`measurableSet_mem_dom_cfChart_comp`,
  `measurable_indicator_fwd_cfChart_comp`, `measurable_indicator_lift_cfChart_comp`);
* `jwL`, `jwR`: the image word's weights with the junction weights as parameters (PROVE-GLUECOND5's `imgρL`,
  `imgρR` are the case `cL5`, `cR5`; PROVE-GLUECOND6's half-plane computation gives `cL6`, `cR6`);
  `ImageWord49FiltWStatement cL cR` (PROVE-GLUECOND5's martingale clause with these weights);
* `ImgChartConst49Statement cL cR` (**named input**, the chart clause at fixed image times; Astra's E.3–E.6 at
  general `κ`);
* **`imageWord49FiltWStatement_of_chartConst`**: `ImgChartConst49Statement cL cR → ImageWord49FiltWStatement cL cR`;
* `exists_isWordEntrance_of_filtW`: the word entrance (Lemma 2.11) from the martingale clause, for any junction
  weights.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q
open ImgDrv MartChar Sec7.PhaseSelFull Sec7.Aux117

namespace Word49

/-! ### The chart is known from the stopped counterflow history -/

section ChartMeas

variable {Ω' : Type*} {𝓜 : MeasurableSpace Ω'} {s : ℝ≥0} {Y : Ω' → HistorySpace 0 0}

/-- A function measurable for the stopped-history σ-algebra, read through `Y`, is measurable for any σ-algebra in
which the stopped history of `Y` is measurable. -/
theorem measurable_comp_of_stopSigma {β : Type*} [MeasurableSpace β] {f : HistorySpace 0 0 → β}
    (hf : Measurable[stopSigma s] f) (hY : Measurable[𝓜] fun p => cfStop s (Y p)) : Measurable[𝓜] (f ∘ Y) := by
  intro B hB
  obtain ⟨C, hC, hfC⟩ := hf hB
  rw [Set.preimage_comp, ← hfC, ← Set.preimage_comp]
  exact hY hC

theorem measurableSet_comp_of_stopSigma {A : Set (HistorySpace 0 0)} (hA : MeasurableSet[stopSigma s] A)
    (hY : Measurable[𝓜] fun p => cfStop s (Y p)) : MeasurableSet[𝓜] (Y ⁻¹' A) := by
  obtain ⟨C, hC, hAC⟩ := hA
  rw [← hAC, ← Set.preimage_comp]
  exact hY hC

theorem measurableSet_mem_dom_cfChart_comp (hY : Measurable[𝓜] fun p => cfStop s (Y p)) (z : ℂ) :
    MeasurableSet[𝓜] {p | z ∈ (cfChart s (Y p)).dom} :=
  measurableSet_comp_of_stopSigma (measurableSet_mem_dom_cfChart z) hY

theorem measurable_indicator_fwd_cfChart_comp (hY : Measurable[𝓜] fun p => cfStop s (Y p)) (z : ℂ) :
    Measurable[𝓜] ({p | z ∈ (cfChart s (Y p)).dom}.indicator fun p => (cfChart s (Y p)).1 z) :=
  measurable_comp_of_stopSigma (measurable_indicator_fwd_cfChart z) hY

theorem measurable_indicator_lift_cfChart_comp (hY : Measurable[𝓜] fun p => cfStop s (Y p)) (z : ℂ) :
    Measurable[𝓜] ({p | z ∈ (cfChart s (Y p)).dom}.indicator fun p => (cfChart s (Y p)).2.2 z) :=
  measurable_comp_of_stopSigma (measurable_indicator_lift_cfChart z) hY

end ChartMeas

/-! ### The junction weights of the image word -/

section Weights

variable {nL nR : ℕ}

/-- **The left weights of the image word with junction weight `cL κ (Σ ρ_L)`**: the flow word's left weights and one
junction weight for the exposed left side of the counterflow. -/
def jwL (cL : ℝ → ℝ → ℝ) (κ : ℝ) (ρL : Fin nL → ℝ) : Fin (nL + 1) → ℝ := Fin.snoc ρL (cL κ (∑ i, ρL i))

/-- **The right weights of the image word with junction weight `cR κ (Σ ρ_R)`.** -/
def jwR (cR : ℝ → ℝ → ℝ) (κ : ℝ) (ρR : Fin nR → ℝ) : Fin (nR + 1) → ℝ := Fin.snoc ρR (cR κ (∑ j, ρR j))

/-- PROVE-GLUECOND5's left junction weight `κ/2 − 2 − Σρ_L` (from Remark 4.10's strip heights `−λ + πχ`). -/
def cL5 (κ σ : ℝ) : ℝ := κ / 2 - 2 - σ

/-- PROVE-GLUECOND5's right junction weight `−Σρ_R` (from Remark 4.10's strip height `λ`). -/
def cR5 (_κ σ : ℝ) : ℝ := -σ

/-- **The left junction weight `κ − 4 − Σρ_L` of the half-plane chart `Ψ`** (PROVE-GLUECOND6's computation of the
counterflow mean in the chart `Ψ` with the lift normalized at the physical real line, `GlueCondUnionImgMean`: exposed
left height `−λ + 2πχ`). -/
def cL6 (κ σ : ℝ) : ℝ := κ - 4 - σ

/-- **The right junction weight `κ/2 − 2 − Σρ_R` of the half-plane chart `Ψ`** (exposed right height `λ − πχ`). -/
def cR6 (κ σ : ℝ) : ℝ := κ / 2 - 2 - σ

theorem jwL_cL5 (κ : ℝ) (ρL : Fin nL → ℝ) : jwL cL5 κ ρL = imgρL κ ρL := rfl

theorem jwR_cR5 (κ : ℝ) (ρR : Fin nR → ℝ) : jwR cR5 κ ρR = imgρR ρR := rfl

end Weights

/-- **The martingale clause of the image word with junction weights `cL`, `cR`** (PROVE-GLUECOND5's
`ImageWord49FiltStatement` with the junction weights as parameters; `ImageWord49FiltStatement` is the case
`cL5`, `cR5`, `imageWord49FiltStatement_iff`). -/
def ImageWord49FiltWStatement (cL cR : ℝ → ℝ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfField κ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ s : ℝ≥0, 0 < s → ∀ z ∈ H,
          IsLocalMartingaleBefore
            (imgFilt (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) xL xR s ζ W
              (glueGood (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) s ζ W))
            (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
            (fun p => min (QuantumZipper.swallowTime (wpath (imgW s ζ W
                (glueGood (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) s ζ W))
                p) z : WithTop ℝ≥0)
              (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                ((measurable_cfField κ).comp hC.2.1)) s ζ W) p))
            (coupProc κ (jwL cL κ ρL) (jwR cR κ ρR)
              (imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                ((measurable_cfField κ).comp hC.2.1)) s ζ W))
              (imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                ((measurable_cfField κ).comp hC.2.1)) s ζ W))
              (imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
                ((measurable_cfField κ).comp hC.2.1)) s ζ W)) z)

/-- **The corrected martingale clause of the image word** (junction weights `cL6 = κ − 4 − Σρ_L`,
`cR6 = κ/2 − 2 − Σρ_R`; the evidence that these, and not PROVE-GLUECOND5's `cL5`, `cR5`, are the weights of the
counterflow chart is in `CrossCondMartWeights`). -/
def ImageWord49FiltCStatement : Prop := ImageWord49FiltWStatement.{u} cL6 cR6

/-- PROVE-GLUECOND5's martingale clause is the case of the junction weights `cL5`, `cR5`. -/
theorem imageWord49FiltStatement_iff : ImageWord49FiltStatement.{u} ↔ ImageWord49FiltWStatement.{u} cL5 cR5 :=
  Iff.rfl

/-! ### The chart clause at fixed image times and the martingale clause -/

/-- **Named input: the chart coupling clause of the image word at fixed image times** (Astra's E.3–E.6 at general
`κ`: the history-marked union law, the identification of the union mean in the chart `Ψ`, the optional passage of the
conditional characteristic functions to the image times and the random chart). In the setting of
`Prop411Q.CfGlueAE`, for each counterflow time `s > 0`, at every fixed image time `r`, for every choice `u` of the
bounded harmonic extensions of the image word's data at `r` and every test function `φ`, almost surely on
`{r < imgT} ∩ {supp φ ⊆ Ψ⁻¹(ℍ ∖ K̃_r)}` the conditional characteristic function of `(h, φ)` given the raw image
filtration `imgRaw r` is that of the image coupling mean pulled back by the chart `Ψ` (lift coefficient `χ`, height
shift `2πχ`) plus a zero-boundary GFF on `Ψ⁻¹(ℍ ∖ K̃_r)` (`Lemma71D.IsChartCouplingCharFunConst` with the chart
`cfChart`). -/
def ImgChartConst49Statement (cL cR : ℝ → ℝ → ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → Sec4.Cond44 κ ρL ρR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (h₂ : Ω₂ → DistOn upperHalfPlaneOpens) (W₂ : ℝ≥0 → Ω₂ → ℝ) (ζ₂ : Ω₂ → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂ →
      P.map (fun ω => cfField κ (h ω)) = P₂.map h₂ →
      ∀ (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k],
        P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k →
        ∀ s : ℝ≥0, 0 < s →
          Sec7.Lemma71D.IsChartCouplingCharFunConst κ (jwL cL κ ρL) (jwR cR κ ρR)
            (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))
            (imgRaw xL xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) s ζ W))
            (imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) s ζ W))
            (imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) s ζ W))
            (imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) s ζ W))
            (fun p => (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
              ((measurable_cfField κ).comp hC.2.1)) s ζ W) p : ℝ≥0∞))
            (fun p => cfChart s p.2) (2 * Real.pi * chiC κ) (chiC κ) (fun p => h p.1)

/-- **The martingale clause of the image word from the chart clause at fixed image times** (general-`κ` step B4):
the clause is lifted to every stopping time of `imgFilt`, transported to `ℍ` through the chart `Ψ` (lift `Im L_Ψ`,
coefficient `χ`, height shift `2πχ`), and turned into local martingales of the explicit coupling means of the image
word (Lemma 7.1's pipeline, with the random initial word allowed). -/
theorem imageWord49FiltWStatement_of_chartConst {cL cR : ℝ → ℝ → ℝ} (hI : ImgChartConst49Statement.{u} cL cR) :
    ImageWord49FiltWStatement.{u} cL cR := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk s hs
    z hz
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hE : MeasurableSet E := measurableSet_glueGood
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  have hWad : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
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
  have hcf0 := hI κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs
  have hcfU : Coupling.MartMeans2.IsChartCouplingCharFun κ (jwL cL κ ρL) (jwR cR κ ρR) μ 𝓖 (imgW s ζ W E)
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
  have hcf' : Coupling.MartMeans.IsCouplingCharFun κ (jwL cL κ ρL) (jwR cR κ ρR) μ 𝓖 (imgW s ζ W E)
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
    hT hint hcf' (fun p t => meanExt κ (jwL cL κ ρL) (jwR cR κ ρR) (imgW s ζ W E t p)
      (fun i => imgVL xL s ζ W E i t p) (fun j => imgVR xR s ζ W E j t p))
    (fun p t => isBoundedHarmonicExtension_meanExt κ (jwL cL κ ρL) (jwR cR κ ρR) _ _ _) hz
  exact Restart.ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG hGae
    (Restart.ConverseBefore.measurable_coupProc_zero hK.w_zero (fun i => measurable_imgVL xL hWad hE hEg i 0)
      (fun j => measurable_imgVR xR hWad hE hEg j 0) hz) hloc

/-- PROVE-GLUECOND5's martingale clause (junction weights `cL5`, `cR5`) from the chart clause with the same weights. -/
theorem imageWord49FiltStatement_of_chartConst (hI : ImgChartConst49Statement.{u} cL5 cR5) :
    ImageWord49FiltStatement.{u} :=
  imageWord49FiltWStatement_of_chartConst hI

/-- **G4 in Proposition 4.9's direction from the martingale clause, for any junction weights** (PROVE-GLUECOND5's
`exists_isWordEntrance_of_filt` with the junction weights as parameters): on `μ ⊗ P₀` there is a Brownian motion of the
product filtration driving, almost surely, the integrated `SLE_κ(ρ′)` equations of the image word on `[0, imgT)`. -/
theorem exists_isWordEntrance_of_filtW {cL cR : ℝ → ℝ → ℝ} (hI : ImageWord49FiltWStatement.{u} cL cR) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (h44 : Sec4.Cond44 κ ρL ρR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {s : ℝ≥0} (hs : 0 < s) :
    ∃ (Ω₀ : Type) (m₀ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (𝓦 : Filtration ℝ≥0 m₀) (Bi : ℝ≥0 → (Ω × HistorySpace 0 0) × Ω₀ → ℝ),
      IsFilteredBrownianReal (WholeField.prodFiltration
        (imgFilt (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) xL xR s ζ W
          (glueGood (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) s ζ W)) 𝓦)
        Bi ((glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)).prod P₀) ∧
      (∀ p, Continuous fun t => Bi t p) ∧
      ∀ᵐ p ∂((glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)).prod P₀),
        IsWordEntrance κ
          (fun i => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) i 0 p.1)
          (fun j => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) j 0 p.1)
          (jwL cL κ ρL) (jwR cR κ ρR)
          (fun t => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) t p.1)
          (fun i t => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) i t p.1)
          (fun j t => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) j t p.1)
          (fun t => Bi t p)
          (imgT s ζ W (glueGood (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) s ζ W) p.1 : ℝ≥0∞) := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  have hW : AdaptedBefore 𝓕 ζ W := hC.1.2.1
  have hae : ∀ᵐ p ∂μ, IsGood49 s ζ W p := by
    filter_upwards [cfGlueAE_isGood49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf
      hlaw k hk] with p hp
    exact isGood49_of_mem hp.1 hp.2
  obtain ⟨hnull, hK, hWa, hVLa, hVRa, hσ, hσm, hσT, hσlim, -⟩ := filtClauses (xL := xL) (xR := xR) hW hF hae
  exact hK.exists_isWordEntrance hκ hnull hWa hVLa hVRa hσ hσm hσT hσlim
    (hI κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk s hs)

end Word49

end InteractingSLE.Sec5.CrossCond
