/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondThetaMean
import InteractingSLE.Spec.Sec5.CrossCondThetaImg

/-!
# The cross-conditioning law at relative angle `θ`: the mean identification

Packet PROVE-CROSSCOND-THETA. **`MeanIdentThetaStatement θ`** (G3 (ii) at a general relative angle `θ`): on the glued
space of the flow line of `h` and the counterflow of `h − θχ`, the conditional mean of the field given both stopped
histories, read in the counterflow chart, is the chart mean of the killed image word with the junction weights
`cLT θ`, `cRT θ`. **Proved for every `θ`** (`meanIdentThetaStatement`), under the setting's hypotheses (`0 < κ < 4`, an
ordered (4.4) word, `CfThetaBounds κ θ`). At `θ = π/2` it gives the landed `Word49.meanIdent49Statement`
(`meanIdent49Statement_of_theta`).

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CrossCond.Theta

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar MartChar.RealFlow Word49 Sec7.StripSysField
open Sec7.Lemma71C (capClock)

/-- **The mean identification at relative angle `θ`** (θ-version of `Word49.MeanIdent49Statement`,
`Sec5.CrossCondMartFwd`): in the glued setting with the counterflow of `h − θχ`, for each counterflow time `s > 0`,
flow time `t > 0` and test function `φ`, almost surely on the validity event `cfAv φ t`, the conditional mean of
`(h − 𝔥₀)(φ)` given the germs of `A_t ∪ G_s` and both stopped histories, plus `∫ 𝔥₀ φ`, is the chart mean of the
killed image word at `σ(t)` with the junction weights `cLT θ`, `cRT θ` (chart `cfChart`, height shift `2πχ`, lift
coefficient `χ`). -/
def MeanIdentThetaStatement (θ : ℝ) : Prop :=
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
        ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀ →
        ∀ s : ℝ≥0, 0 < s → ∀ t : ℝ≥0, 0 < t → ∀ φ : TestOn upperHalfPlaneOpens,
          ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
            p ∈ cfAv s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
              ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) φ t →
            (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
                fun p' => cenTT κ θ u₀ (cfFieldT κ θ (h p'.1)) φ |
                germSigma (fun p : Ω × HistorySpace 0 0 => hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)
                  (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔ cfGlueMarks W VL VR ζ t s] p +
                ∫ z, u₀ z * φ z =
              Sec7.Lemma71D.chartMean κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
                (fun r => imgW s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                  ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) r p)
                (fun i r => imgVL xL s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                  ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) i r p)
                (fun j r => imgVR xR s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                  ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) j r p)
                (cfChart s p.2) (2 * Real.pi * chiC κ) (chiC κ) φ
                (capClock (gCurve s ζ W (glueGood (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
                  ((measurable_cfFieldT κ θ).comp hC.2.1)) s ζ W) p) t).toNNReal

/-- **The mean identification at relative angle `θ` holds** (θ-version of `Word49.meanIdent49Statement`,
`Sec5.GlueCondUnionImgAssemblyMean`; the landed proof with the θ-versions of the setting lemmas and of the per-sample
chart mean `chartMean_eq_integral_of_sampleT`). -/
theorem meanIdentThetaStatement (θ : ℝ) : MeanIdentThetaStatement.{u} θ := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 hθb Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk u₀
    hu₀ s hs t ht φ
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  set U : Ω × HistorySpace 0 0 → Set ℂ := fun p => hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2
    with hUdef
  set Fd : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)) with hFdef
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
  have hloc := (isLocalSet_union_glueT hC hζ hcf hreg₂ hlaw hk hu₀ t s).2.2
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hFg hAm hloc
  have hce := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hFg hAm hloc hℋ hmark hg φ
  -- the bounded harmonic extensions
  set bd : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(θ * chiC κ) with hbd
  obtain ⟨u', hu'⟩ : ∃ u' : ℂ → ℝ, IsBoundedHarmonicExtension (cfWordData κ bd (forceJumpFinset xL xR))
      (cfWordJumps κ bd (forceJumpFinset xL xR)) u' := by
    obtain ⟨u', hu'⟩ := exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
      (flowLineRhoL (16 / κ) (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0 0)
      (flowLineRhoR (16 / κ) (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0 0)
      (flowLineXL (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0)
      (flowLineXR (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0)
    refine ⟨u', ?_⟩
    simp only [cfWordData, cfWordJumps, coe_forceJumpFinset]
    exact hu'
  choose uq huq using fun ω => exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
    (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)
  have hwA := ae_union_mean_cfGlueT hC hκ hζ hcf hreg₂ hlaw hk hu₀ t s hu' huq hg
  obtain ⟨gG, hgG, hidG⟩ := exists_isLocalSetMean_cfHullQ_pathT hC hκ hcf hreg₂ hlaw hk hu₀ s hu'
  have hInf := ae_tendsto_union_sub_cfMean_coboundedT hC hζ hcf hreg₂ hlaw hk hu₀ t s hg hgG
  have huniq := Sec6.ae_eqOn_component_of_tendsto_global hFg hAm hloc hg hu₀.1 hu₀.2.1 (chiC κ)
  -- almost-sure regularity
  have hgood := cfGlueAE_isGood49T θ s hs κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have himg := cfGlueAE_exists_imageTraceT θ κ hκ hκ4 xL xR ρL ρR hF h44 hθb P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw
      k hk
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1)
  have hmarksP : ∀ᵐ ω ∂P, Continuous (fun r : ℝ => W r.toNNReal ω) ∧ W 0 ω = 0 ∧
      (fun i => VL i t ω - W t ω) =
        (fun i => -rightImg (fun r => -(fun r : ℝ => W r.toNNReal ω) r) (-xL i) t - (fun r : ℝ => W r.toNNReal ω) t) ∧
      (fun i => VR i t ω - W t ω) =
        (fun j => rightImg (fun r : ℝ => W r.toNNReal ω) (xR j) t - (fun r : ℝ => W r.toNNReal ω) t) := by
    filter_upwards [hC.1.2.2.2.2, hζ] with ω hp hζω
    have hw : Continuous fun t => W t ω := by
      have := hp.2.2.2.1
      rw [hζω] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    have hts : ((t : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
    refine ⟨hw.comp continuous_real_toNNReal, hp.1, funext fun i => ?_, funext fun i => ?_⟩
    · rw [WangWu.vL_eq_neg_rightImg hp hw hts i]
      show _ = -rightImg (fun r => -W r.toNNReal ω) (-xL i) t - W (t : ℝ).toNNReal ω
      rw [Real.toNNReal_coe]
      rfl
    · rw [WangWu.vR_eq_rightImg hp hw hts i]
      show _ = rightImg (fun r : ℝ => W r.toNNReal ω) (xR i) t - W (t : ℝ).toNNReal ω
      rw [Real.toNNReal_coe]
      rfl
  have hmarks := ae_glue_fst (μ := P) k hXm hmarksP
  have hAae' := ae_glue_fst (μ := P) k hXm hAae
  filter_upwards [hce, hwA, hInf, huniq, hidG, hgood, himg, hline, hmarks, hAae'] with p hcep
    ⟨w, hwh, hwrep, hwFl, hwG⟩ hInfp huniqp hidGp ⟨_, hy⟩ himgp ⟨_, ⟨η, hη, hseq⟩, _⟩ ⟨hWα, hW0, hmL, hmR⟩ hAp hAv
  obtain ⟨hpE, htP, hav⟩ := hAv
  have hα : IsLoewnerTrace (fun r : ℝ => W r.toNNReal p.1) (seedLine ζ W p.1) := by
    rw [hseq]; exact isLoewnerTrace_of_isGeneratingTrace hη
  have hWα0 : (fun r : ℝ => W r.toNNReal p.1) 0 = 0 := by simp only [Real.toNNReal_zero, hW0]
  have hset := cfChart_inv_image_eq hEg hpE htP (hAp.2 t)
  have hφC : tsupport φ ⊆ H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2) := by
    have := hav.2
    rwa [hset] at this
  have huA := huq p.1
  rw [hmL, hmR] at huA
  have hwInf := hInfp w (cfMeanQ κ bd (forceJumpFinset xL xR) u' s p.2) hwh hwrep
    (harmonicOnNhd_cfMeanQ κ bd (forceJumpFinset xL xR) hu'.1 s p.2) hidGp
  have hmean := chartMean_eq_integral_of_sampleT hκ hF.2.1 hF.2.2.2 hEg hpE ht htP hα hWα hWα0 (hAp.2 t) hy.1 himgp
    hu₀ hu' huA hwFl hwG hwInf (fun z₀ hz₀ => huniqp z₀ hz₀ w hwh hwrep) hφC
  rw [hmean, ← hcep, hwrep φ hφC]
  have hwc : ContinuousOn w (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) :=
    fun z hz => (hwh z hz).1.continuousAt.continuousWithinAt
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hi1 := WholeField.integrable_mul_testOn hwc φ hφC
  have hi2 := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
  rw [← integral_add hi1 hi2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  ring


/-- **At `θ = π/2` the mean identification is the landed one** (`cfFieldT κ (π/2) = cfField κ`,
`cenTT κ (π/2) = cenT κ` definitionally, `cLT (π/2) = cL6`, `cRT (π/2) = cR6`, and (4.4) gives `CfThetaBounds`). -/
theorem meanIdent49Statement_of_theta (hT : MeanIdentThetaStatement.{u} (π / 2)) : MeanIdent49Statement.{u} cL6 cR6 :=
    by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44
  rw [← cLT_pi_div_two, ← cRT_pi_div_two]
  exact hT κ hκ hκ4 xL xR ρL ρR hF h44 (cfThetaBounds_of_cond44 hκ hκ4 hF h44)

/-- The landed `meanIdent49Statement` re-derived from the general-angle theorem. -/
theorem meanIdent49Statement' : MeanIdent49Statement.{u} cL6 cR6 :=
  meanIdent49Statement_of_theta (meanIdentThetaStatement (π / 2))

end InteractingSLE.Sec5.CrossCond.Theta
