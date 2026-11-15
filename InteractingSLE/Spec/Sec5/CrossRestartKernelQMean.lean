/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQSample
import InteractingSLE.Spec.Sec5.GlueCondUnionImgAssemblyMean

/-!
# Lemma 4.7 in the chart `Q`: the conditional mean given both stopped histories, in the image chart of the counterflow

Packet PROVE-CFRESTART3 (PROVE-CFRESTART2's "What remains" 2–3 in the chart `Q`; the mirror of PROVE-GLUECOND10's
`meanIdent49Statement` with the two curves exchanged). On the glued space of `Prop411Q.CfGlueAE`, at a flow time
`q > 0` and a counterflow time `t`:

**`ae_condExp_cfGlue_eq_imgChart47`**: almost surely, if `supp φ` misses `A_q ∪ G_t` (the flow hull and the
counterflow hull read in the chart `Q`), then for every image chain `W′` of the counterflow in the chart
`Ψ = revChart Wβ q` of `ℍ ∖ R(K_q)` (`IsCfImgSetup (cfDrv y) (histLine y) t Wβ q W′ η′ T`, `Wβ` the flow driver) and
every bounded harmonic extension `u` of the image word's data at `T` (the counterflow word mapped by `Ψ`, with the
junction marks and the weights `slitRhoL/R ρ′ κ (π/2)`), the conditional mean of the centred field given the germ of
`A_q ∪ G_t` and both stopped histories, plus `∫ 𝔥₀ φ`, is

`∫ (−u ∘ f′_T ∘ Ψ ∘ R − π/2 χ − χ (Im L′_T ∘ Ψ ∘ R + Im L_Ψ ∘ R − 2 arg)) φ`.

The image chain is allowed to be any continuous driver of the image hull (the killed process-level image word of the
non-simple counterflow is not built yet; when it is, this identifies its explicit mean at the image time of `t`).

## Proof

The union `A_q ∪ G_t` is a local set of the centred field on the glued space (PROVE-GLUECOND); its local-set mean is the
conditional mean given the germs and both stopped histories (`WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup`);
almost surely its harmonic representative has GLUECOND's two boundary limits (`GlueCond.ae_union_mean_cfGlue`) and
Aux. 28's uniqueness (`Sec6.ae_eqOn_component_of_tendsto_global`); on a good sample (proper flow line, good
counterflow history) these are the hypotheses of `KernelQ.eqOn_imgChart_cfGlue` once the hulls and the counterflow's
mean are read from the drivers (`hullAt_eq_fwdHull_of_mem_goodCfSet`, `rpath_regPath_cfStop_eq`, driver congruence on
`[0, t]`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Metric Filter Topology
open scoped NNReal ENNReal Real

open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79 Sec7.StripSysField GlueCond Cond44Ref CrossCond.Theta GlueImg
open LawUnique Prop411Q CfRegQ WholeField LocalSets CrossCond CrossCond.Word49

/-! ### The counterflow's mean read from its driver -/

section Drv

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {y : HistorySpace 0 0}

/-- On a good history, the counterflow mean `cfMeanQ` is the chart-`R` coupling mean of the driver `cfDrv y`. -/
theorem cfMeanQ_eq_of_mem_goodCfSet (hy : y ∈ goodCfSet) (u' : ℂ → ℝ) (t : ℝ≥0) (z : ℂ) :
    cfMeanQ κ b J u' t y z =
      -couplingMean (16 / κ) (cfDrv y) t (cfU κ b J t (cfStop t y)) (negInv z) + u' (negInv z) := by
  have he : EqOn (Ito.rpath (Sec4.regPath (cfStop t y))) (cfDrv y) (Icc 0 (t : ℝ)) := fun r hr => by
    rw [rpath_regPath_cfStop_eq hy t]
    exact cfDrv0_eq_cfDrv hy hr
  simp only [cfMeanQ, couplingMean]
  rw [Ito.fwdMap_congr_of_eqOn he, Ito.logDerivFwd_congr_of_eqOn he t.coe_nonneg le_rfl]

/-- On a good history, the counterflow word's harmonic extension `cfU` at `t` has the data flowed by `cfDrv y`. -/
theorem isBoundedHarmonicExtension_cfU_of_mem_goodCfSet (hy : y ∈ goodCfSet) (t : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData (16 / κ) (cfRhoL κ b J) (cfRhoR κ b J)
        (fun i => -rightImg (fun r => -cfDrv y r) (-flowLineXL (counterflowData κ b) (counterflowJumps J) 0 i) t -
          cfDrv y t)
        (fun j => rightImg (cfDrv y) (flowLineXR (counterflowData κ b) (counterflowJumps J) 0 j) t - cfDrv y t))
      (forceJumpSet
        (fun i => -rightImg (fun r => -cfDrv y r) (-flowLineXL (counterflowData κ b) (counterflowJumps J) 0 i) t -
          cfDrv y t)
        (fun j => rightImg (cfDrv y) (flowLineXR (counterflowData κ b) (counterflowJumps J) 0 j) t - cfDrv y t))
      (cfU κ b J t (cfStop t y)) := by
  have h1 := isBoundedHarmonicExtension_cfU κ b J t (cfStop t y)
  have hw : Continuous (cfDrv y) := (reg_of_mem_goodCfSet hy).2.1
  have he : EqOn (Ito.rpath (Sec4.regPath (cfStop t y))) (cfDrv y) (Icc 0 (t : ℝ)) := fun r hr => by
    rw [rpath_regPath_cfStop_eq hy t]
    exact cfDrv0_eq_cfDrv hy hr
  have hen : EqOn (fun r => -Ito.rpath (Sec4.regPath (cfStop t y)) r) (fun r => -cfDrv y r) (Icc 0 (t : ℝ)) :=
    fun r hr => by simp only [he hr]
  have ht : Sec4.regPath (cfStop t y) t = cfDrv y t := by
    have h2 := he ⟨t.coe_nonneg, le_rfl⟩
    simp only [Ito.rpath, Real.toNNReal_coe] at h2
    exact h2
  have hL : cfPosL κ b J (Sec4.regPath (cfStop t y)) t =
      fun i => -rightImg (fun r => -cfDrv y r) (-flowLineXL (counterflowData κ b) (counterflowJumps J) 0 i) t -
        cfDrv y t := by
    funext i
    simp only [cfPosL]
    rw [Sec7.Lemma71B.rightImg_congr (show Continuous fun r => -cfDrv y r from hw.neg) t.coe_nonneg hen, ht]
  have hR : cfPosR κ b J (Sec4.regPath (cfStop t y)) t =
      fun j => rightImg (cfDrv y) (flowLineXR (counterflowData κ b) (counterflowJumps J) 0 j) t - cfDrv y t := by
    funext j
    simp only [cfPosR]
    rw [Sec7.Lemma71B.rightImg_congr hw t.coe_nonneg he, ht]
  rw [hL, hR] at h1
  exact h1

end Drv

/-! ### The conditional mean on the glued space -/

section Main

/-- **Lemma 4.7's direction in the chart `Q`: the conditional mean of the field given the flow prefix at `q` and the
counterflow prefix at `t`, read in the image chart of the counterflow** (see the module docstring). -/
theorem ae_condExp_cfGlue_eq_imgChart47 {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (q t : ℝ≥0) (hq : 0 < q) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      tsupport φ ⊆ H \ (hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) →
      ∀ (W' : ℝ → ℝ) (η' : ℝ → ℂ) (T : ℝ),
        IsCfImgSetup (cfDrv p.2) (histLine p.2) t (fun r : ℝ => W r.toNNReal p.1) q W' η' T →
      ∀ u : ℂ → ℝ, IsBoundedHarmonicExtension
        (forceBoundaryData (16 / κ) (slitRhoL (qρL κ ρL ρR xL xR) κ (π / 2))
          (slitRhoR (qρR κ ρL ρR xL xR) κ (π / 2))
          (fun i => -rightImg (fun r => -W' r)
            (-imgMarkL (qxL κ ρL ρR xL xR) (fun r : ℝ => W r.toNNReal p.1) q i) T - W' T)
          (fun j => rightImg W' (imgMarkR (qxR κ ρL ρR xL xR) (fun r : ℝ => W r.toNNReal p.1) q j) T - W' T))
        (forceJumpSet
          (fun i => -rightImg (fun r => -W' r)
            (-imgMarkL (qxL κ ρL ρR xL xR) (fun r : ℝ => W r.toNNReal p.1) q i) T - W' T)
          (fun j => rightImg W' (imgMarkR (qxR κ ρL ρR xL xR) (fun r : ℝ => W r.toNNReal p.1) q j) T - W' T)) u →
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
          fun p' => cenT κ u₀ (cfField κ (h p'.1)) φ |
          germSigma (fun p : Ω × HistorySpace 0 0 => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
            (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ q t] p +
          ∫ z, u₀ z * φ z =
        ∫ z, (-u (fwdMap W' T (revChart (fun r : ℝ => W r.toNNReal p.1) q (negInv z))) - π / 2 * chiC κ -
          chiC κ * ((logDerivFwd W' T (revChart (fun r : ℝ => W r.toNNReal p.1) q (negInv z))).im +
            (logDerivPsi (fun r : ℝ => W r.toNNReal p.1) q (negInv z)).im - 2 * arg z)) * φ z := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set U : Ω × HistorySpace 0 0 → Set ℂ := fun p => hullAt q (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2
    with hUdef
  have hX := hC.2.2.2.1
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hFg := isZeroBoundaryGFF_cenT_glue (k := k) hC hu₀
  have hAm : Measurable[_, hittingSigma] U :=
    measurable_union_hitting (((measurable_hullAt q).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ t).comp measurable_snd)
  have hAae := ae_hullAt_eq_image_seedLine hκ hκ4 hF h44 hC
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hAae] with ω hω using hω.1
  have hreg₂ := ae_cfReg hκ hκ4 hF h44 hC hcf hlaw
  have hmark := isHistoryAvoidanceLocal_cfGlue hC hκ hζ hcf hreg₂ hlaw hk hu₀ q t
  have hℋ := cfGlueMarks_le (Ω := Ω) q t hX
  have hloc := (isLocalSet_union_glue hC hζ hcf hreg₂ hlaw hk hu₀ q t).2.2
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hFg hAm hloc
  have hce := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hFg hAm hloc hℋ hmark hg φ
  -- the bounded harmonic extensions
  set bd : ℝ → ℝ := bData ρL ρR xL xR κ with hbd
  obtain ⟨u', hu'⟩ : ∃ u' : ℂ → ℝ, IsBoundedHarmonicExtension (cfWordData κ bd (forceJumpFinset xL xR))
      (cfWordJumps κ bd (forceJumpFinset xL xR)) u' := by
    obtain ⟨u', hu'⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
      (flowLineRhoL (16 / κ) (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0 0)
      (flowLineRhoR (16 / κ) (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0 0)
      (flowLineXL (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0)
      (flowLineXR (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0)
    refine ⟨u', ?_⟩
    simp only [cfWordData, cfWordJumps, coe_forceJumpFinset]
    exact hu'
  choose uq huq using fun ω => Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
    (fun i => VL i q ω - W q ω) (fun i => VR i q ω - W q ω)
  have hwA := ae_union_mean_cfGlue hC hκ hζ hcf hreg₂ hlaw hk hu₀ q t hu' huq hg
  have huniq := Sec6.ae_eqOn_component_of_tendsto_global hFg hAm hloc hg hu₀.1 hu₀.2.1 (chiC κ)
  -- almost-sure regularity
  have hgood := cfGlueAE_mem_goodHitSet κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1)
  have hmarksP : ∀ᵐ ω ∂P, (fun i => VL i q ω - W q ω) =
        (fun i => -rightImg (fun r => -(fun r : ℝ => W r.toNNReal ω) r) (-xL i) q - (fun r : ℝ => W r.toNNReal ω) q) ∧
      (fun i => VR i q ω - W q ω) =
        (fun j => rightImg (fun r : ℝ => W r.toNNReal ω) (xR j) q - (fun r : ℝ => W r.toNNReal ω) q) := by
    filter_upwards [hC.1.2.2.2.2, hζ] with ω hp hζω
    have hw : Continuous fun t => W t ω := by
      have := hp.2.2.2.1
      rw [hζω] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    have hts : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
    refine ⟨funext fun i => ?_, funext fun i => ?_⟩
    · rw [WangWu.vL_eq_neg_rightImg hp hw hts i]
      show _ = -rightImg (fun r => -W r.toNNReal ω) (-xL i) q - W (q : ℝ).toNNReal ω
      rw [Real.toNNReal_coe]
      rfl
    · rw [WangWu.vR_eq_rightImg hp hw hts i]
      show _ = rightImg (fun r : ℝ => W r.toNNReal ω) (xR i) q - W (q : ℝ).toNNReal ω
      rw [Real.toNNReal_coe]
      rfl
  have hmarks := ae_glue_fst (μ := P) k hXm hmarksP
  have hAae' := ae_glue_fst (μ := P) k hXm hAae
  filter_upwards [hce, hwA, huniq, hgood, hline, hmarks, hAae'] with p hcep ⟨w, hwh, hwrep, hwFl, hwG⟩ huniqp hy
    ⟨_, ⟨η, hη, hseq⟩, hprop⟩ ⟨hmL, hmR⟩ hAp hφ W' η' T hd u hu
  set Wβ : ℝ → ℝ := fun r : ℝ => W r.toNNReal p.1 with hWβdef
  have hβ : IsLoewnerTrace Wβ (seedLine ζ W p.1) := by
    rw [hseq]; exact isLoewnerTrace_of_isGeneratingTrace hη
  have hA : hullAt q (killedHistory W VL VR ζ p.1) = fwdHull Wβ q := by
    rw [hAp.2 q, fwdHull_eq_image_Ioc hβ hprop q.coe_nonneg]
  have hG : cfHullQ t p.2 = negInv '' fwdHull (cfDrv p.2) t := by
    rw [cfHullQ, hullAt_eq_fwdHull_of_mem_goodCfSet hy.1 t]
  simp only [hUdef] at huniqp
  rw [hA, hG] at hwFl hwG huniqp hφ hwh hwrep
  have huq' := huq p.1
  rw [hmL, hmR] at huq'
  have hFG : ∀ z₀ ∈ negInv '' fwdHull (cfDrv p.2) t,
      Tendsto (fun z => w z - (-couplingMean (16 / κ) (cfDrv p.2) t (cfU κ bd (forceJumpFinset xL xR) t
        (cfStop t p.2)) (negInv z) + u' (negInv z)))
        (𝓝[H \ (fwdHull Wβ q ∪ negInv '' fwdHull (cfDrv p.2) t)] z₀) (𝓝 0) := by
    intro z₀ hz₀
    have hcond : ∃ r > 0, fwdHull Wβ q ∩ ball z₀ r ⊆ negInv '' fwdHull (cfDrv p.2) t := by
      have hncl : z₀ ∉ closure (fwdHull Wβ q) := fun h => disjoint_left.1 hd.hdis h (subset_closure hz₀)
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl z₀ hncl
      exact ⟨r, hr, fun z hz => absurd (subset_closure hz.1) (hball hz.2)⟩
    refine (hwG z₀ (Or.inl hz₀) hcond).congr fun z => ?_
    rw [cfMeanQ_eq_of_mem_goodCfSet hy.1]
  have huA := isBoundedHarmonicExtension_cfU_of_mem_goodCfSet (κ := κ) (b := bd) (J := forceJumpFinset xL xR)
    hy.1 t
  have hid := eqOn_imgChart_cfGlue hd hκ hκ4 (NNReal.coe_pos.2 hq) hβ hprop ρL ρR hF.2.1 hF.2.2.2 hu₀ huq' hu' huA hu
    hwFl hFG (fun z₀ hz₀ => huniqp z₀ hz₀ w hwh hwrep)
  rw [← hcep, hwrep φ hφ]
  have hwc : ContinuousOn w (H \ (fwdHull Wβ q ∪ negInv '' fwdHull (cfDrv p.2) t)) :=
    fun z hz => (hwh z hz).1.continuousAt.continuousWithinAt
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hi1 := WholeField.integrable_mul_testOn hwc φ hφ
  have hi2 := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
  rw [← integral_add hi1 hi2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : φ z = 0
  · simp [hz]
  · have hzD := hφ (subset_tsupport _ hz)
    simp only
    rw [← add_mul, hid z hzD]

end Main

end InteractingSLE.Sec5.CrossRestart.KernelQ
