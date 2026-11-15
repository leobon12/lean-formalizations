/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Lemma47AngleMean
/-!
# Lemma 4.7 at a relative angle: the killed-word chart mean

The killed driver, its chart and its comparison with a local continuous driver are
reused without change. The characteristic-function argument uses the angle-dependent mean.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Complex Set Metric Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
universe u
namespace InteractingSLE.Sec5.Lemma47Angle
open WangWu hiding ratPt exists_ratPt_dist_lt
open MartChar.RealFlow Restart.RetAux79 Sec7.StripSysField GlueCond Cond44Ref CrossCond.Theta GlueImg
open Sec7.Lemma71C (capClock)
open LawUnique Prop411Q CfRegQ WholeField LocalSets CrossCond CrossCond.Word49
open CrossRestart.KernelQ CrossRestart.KernelQ.Kill47
/-- Image word's left weights, including the angle-dependent slit junction. -/
abbrev iwLT (κ θ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) := CrossRestart.slitRhoL (qρLT κ θ ρL ρR xL xR) κ θ
/-- Image word's right weights, including the angle-dependent slit junction. -/
abbrev iwRT (κ θ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) := CrossRestart.slitRhoR (qρRT κ θ ρL ρR xL xR) κ θ

section Ident

variable {κ θ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The conditional mean given both stopped histories is minus the chart mean of the killed image word** (Lemma 4.7
direction of G3 (ii); item D2). -/
theorem ae_condExp_glue_eq_neg_chartMean_angle (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {s : ℝ≥0} (hs : 0 < s) {t : ℝ≥0} (ht : 0 < t) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ qAv W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) φ t →
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
          fun p' => cenTT κ θ u₀ (cfFieldT κ θ (h p'.1)) φ |
          germSigma (fun p : Ω × HistorySpace 0 0 => hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
            (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔ cfGlueMarks W VL VR ζ s t] p +
          ∫ z, u₀ z * φ z =
        -Sec7.Lemma71D.chartMean (16 / κ) (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR)
          (fun r => qW W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) r p)
          (fun i r => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k
            (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) i r p)
          (fun j r => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k
            (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) j r p)
          (fChart W VL VR ζ s p) (-((π - θ) * chiC κ)) (-chiC κ) φ
          (capClock (qgCurve W s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) p) t).toNNReal := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood47 μ W VL VR ζ with hEdef
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 ht
  filter_upwards [ae_condExp_cfGlue_eq_imgChart47_angle hκ hκ4 hF h44 hθb hC hcf hlaw k hk hu₀ s t hs φ] with p hcfr hAv
  obtain ⟨hpE, htP, hav⟩ := hAv
  have hg := hEg p hpE
  set γ := qgCurve W s E p with hγdef
  obtain ⟨W', η', c, hset, hTc, hEq⟩ := exists_isCfImgSetup_q hEg hpE hs ht' htP
  set T := capClock γ t with hTdef
  have hT0 : 0 < T := hset.hT
  have hlt : ((T.toNNReal : ℝ≥0) : WithTop ℝ≥0) < qT W VL VR ζ s E p :=
    (isKilledCurve_qgCurve hEg p).lt_kcLife htP
  have hφ : tsupport φ ⊆ H \ (hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2) := by
    have := hav.2
    rwa [fChart_inv_image_eq hEg hpE htP] at this
  set Wf : ℝ → ℝ := fDrv W p with hWf
  obtain ⟨u, hu⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ) (iwLT κ θ ρL ρR xL xR)
    (iwRT κ θ ρL ρR xL xR)
    (fun i => -rightImg (fun r => -W' r) (-GlueImg.imgMarkL (qxLT κ θ ρL ρR xL xR) Wf s i) T - W' T)
    (fun j => rightImg W' (GlueImg.imgMarkR (qxRT κ θ ρL ρR xL xR) Wf s j) T - W' T)
  have hid := hcfr hφ W' η' T hset u hu
  rw [hid, Sec7.Lemma71D.chartMean, ← integral_neg]
  have hmL : ∀ i, -rightImg (fun r => -W' r) (-GlueImg.imgMarkL (qxLT κ θ ρL ρR xL xR) Wf s i) T - W' T ≤ 0 :=
    fun i => by
      have := le_rightImg (show Continuous fun r => -W' r from hset.hW'.neg)
        (-GlueImg.imgMarkL (qxLT κ θ ρL ρR xL xR) Wf s i) hT0.le
      linarith
  have hmR : ∀ j, 0 ≤ rightImg W' (GlueImg.imgMarkR (qxRT κ θ ρL ρR xL xR) Wf s j) T - W' T := fun j => by
    have := le_rightImg hset.hW' (GlueImg.imgMarkR (qxRT κ θ ρL ρR xL xR) Wf s j) hT0.le
    linarith
  have hAG : fwdHull (cfDrv p.2) t ⊆ H \ negInv '' fwdHull Wf s := fun z hz =>
    ⟨(isHPHull_fwdHull hset.hWα t.coe_nonneg).1 hz, fun h => disjoint_left.1 hset.hdisj hz h⟩
  have hmaps := GlueImg.revChart_mapsTo_H_diff hset.hWβ hset.hWβ0 s.coe_nonneg hAG
  rw [← hset.hK'] at hmaps
  have hyA : hullAt s (killedHistory W VL VR ζ p.1) = fwdHull Wf s := hullAt_flow_of_good hg
  have hyG : cfHullQ t p.2 = negInv '' fwdHull (cfDrv p.2) t := by
    rw [cfHullQ, hullAt_eq_fwdHull_of_mem_goodCfSet hg.2.2.1.1 t]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero, neg_zero]
  have hzC := hφ (subset_tsupport _ hz)
  rw [hyA, hyG] at hzC
  have hnz : negInv z ∈ H \ (fwdHull (cfDrv p.2) t ∪ negInv '' fwdHull Wf s) := by
    refine ⟨WangWu.negInv_mem_H hzC.1, fun hmem => hzC.2 ?_⟩
    rcases hmem with hK | ⟨w, hw, e⟩
    · exact Or.inr ⟨negInv z, hK, WangWu.negInv_negInv z⟩
    · refine Or.inl ?_
      have : w = z := by rw [← WangWu.negInv_negInv w, e, WangWu.negInv_negInv]
      exact this ▸ hw
  have hfH : fwdMap W' T (revChart Wf s (negInv z)) ∈ H :=
    QuantumZipper.FwdHolo.mapsTo_fwdMap hset.hW' hT0.le (hmaps hnz)
  show (_ : ℝ) * φ z = -((Coupling.meanCan (16 / κ) (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR)
      (fun r => qW W VL VR ζ s E r p) (fun i r => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i r p)
      (fun j r => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j r p) T.toNNReal ((fChart W VL VR ζ s p).1 z) -
      -((π - θ) * chiC κ) - -chiC κ * (fChart W VL VR ζ s p).2.2 z) * φ z)
  rw [fChart_fst_eq hg, fChart_lift_eq hg hzC.1, meanCan_q_eq hpE hT0.le hTc.le hlt hset.hW' hEq,
    ← Ito.eqOn_meanHarmonic hmL hmR hu hfH, Sec4.chiC_sixteen_div hκ]
  simp only [hWf]
  unfold fDrv
  ring

/-- **Step R1 (Lemma 4.7 direction).** At a counterflow time `t > 0`, almost surely on the validity event, the
conditional characteristic function of `(−h, φ)` given the germ of `A_s ∪ G_t` and both stopped histories is the
explicit `qF(σ(t))`. -/
theorem ae_condExp_glue_eq_qF_angle (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hθb : CfThetaBounds κ θ ρL ρR xL xR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfFieldT κ θ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {s : ℝ≥0} (hs : 0 < s) {t : ℝ≥0} (ht : 0 < t) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1)),
      p ∈ qAv W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
        ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) φ t →
      (glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * ((-(h p'.1 φ) : ℝ) : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 0 0 => hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
            (fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1))) ⊔ cfGlueMarks W VL VR ζ s t] p =
        qF (16 / κ) (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR) (qxLT κ θ ρL ρR xL xR) (qxRT κ θ ρL ρR xL xR)
          (-((π - θ) * chiC κ)) (-chiC κ) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) φ
          (capClock (qgCurve W s (glueGood47 (glueMeasure P k (fun ω => cfFieldT κ θ (h ω))
            ((measurable_cfFieldT κ θ).comp hC.2.1)) W VL VR ζ) p) t).toNNReal p := by
  set μ := glueMeasure P k (fun ω => cfFieldT κ θ (h ω)) ((measurable_cfFieldT κ θ).comp hC.2.1) with hμ
  set E := glueGood47 μ W VL VR ζ with hEdef
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  set U : Ω × HistorySpace 0 0 → Set ℂ := fun p => hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2
    with hUdef
  set F : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => cenTT κ θ u₀ (cfFieldT κ θ (h p.1)) with hFdef
  have hX := hC.2.2.2.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hFg := isZeroBoundaryGFF_cenTT_glue (θ := θ) (k := k) hC hu₀
  have hAm : Measurable[_, hittingSigma] U :=
    measurable_union_hitting (((measurable_hullAt s).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ t).comp measurable_snd)
  have hAae := CrossCond.Word49.ae_hullAt_eq_image_seedLine hκ hκ4 hF h44 hC
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hAae] with ω hω using hω.1
  have hreg₂ := CrossCond.Theta.ae_cfRegT hκ hθb hC hcf hlaw
  have hmark := isHistoryAvoidanceLocal_cfGlueT hC hκ hζ hcf hreg₂ hlaw hk hu₀ s t
  have hℋ := cfGlueMarks_le (Ω := Ω) s t hX
  obtain ⟨M, -, hM1, hM2⟩ := exists_condExp_germSigma_history hFg hAm hℋ hmark
    (Eventually.of_forall fun p => union_relClosed s t _ p.2) (-φ)
  set c : ℂ := Complex.exp (Complex.I * ((-∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have hFφ : ∀ p : Ω × HistorySpace 0 0, F p φ = h p.1 φ - ∫ z, u₀ z * φ z := fun p => by
    simp only [hFdef, cenTT_cfFieldT]
    rw [show h p.1 - SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ =
      centredField h u₀ p.1 from rfl, centredField_apply h hu₀.1 p.1 φ]
  have e : (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * ((-(h p.1 φ) : ℝ) : ℂ))) =
      c • fun p => Complex.exp (Complex.I * (F p (-φ) : ℂ)) := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, hc, ← Complex.exp_add, map_neg, hFφ]
    congr 1
    push_cast
    ring
  have hpull := condExp_smul (μ := μ) c (fun p : Ω × HistorySpace 0 0 => Complex.exp (Complex.I * (F p (-φ) : ℂ)))
    (germSigma U F ⊔ cfGlueMarks W VL VR ζ s t)
  rw [← e] at hpull
  have hneg : μ[fun p => F p (-φ) | germSigma U F ⊔ cfGlueMarks W VL VR ζ s t] =ᵐ[μ]
      -μ[fun p => F p φ | germSigma U F ⊔ cfGlueMarks W VL VR ζ s t] := by
    have e2 : (fun p : Ω × HistorySpace 0 0 => F p (-φ)) = -(fun p => F p φ) :=
      funext fun p => by simp only [map_neg, Pi.neg_apply]
    rw [e2]
    exact condExp_neg _ _
  have hid := ae_condExp_glue_eq_neg_chartMean_angle hκ hκ4 hF h44 hθb hC hcf hlaw k hk hu₀ hs ht φ
  filter_upwards [hM1, hM2, hpull, hid, hneg] with p h1 h2 h5 h4 h6 hAv
  obtain ⟨hpE, htP, hav⟩ := hAv
  have hset := fChart_inv_image_eq hEg hpE htP
  rw [h5, Pi.smul_apply, ← h2, smul_eq_mul]
  have hMp : M p = Sec7.Lemma71D.chartMean (16 / κ) (iwLT κ θ ρL ρR xL xR) (iwRT κ θ ρL ρR xL xR)
      (fun r => qW W VL VR ζ s E r p) (fun i r => qVL (qxLT κ θ ρL ρR xL xR) W VL VR ζ s E i r p)
      (fun j r => qVR (qxRT κ θ ρL ρR xL xR) W VL VR ζ s E j r p) (fChart W VL VR ζ s p) (-((π - θ) * chiC κ))
      (-chiC κ) φ (capClock (qgCurve W s E p) t).toNNReal + ∫ z, u₀ z * φ z := by
    rw [h1, h6, Pi.neg_apply]
    have := h4 ⟨hpE, htP, hav⟩
    linarith
  have hv : QuantumZipper.zeroGFFTestCov (H \ relClosureH (U p)) ⇑(-φ) ⇑(-φ) =
      Sec7.Lemma71D.chartVar (fun r => qW W VL VR ζ s E r p) (fChart W VL VR ζ s p) φ
        (capClock (qgCurve W s E p) t).toNNReal := by
    obtain ⟨hsub, hopen⟩ := union_relClosed s t (killedHistory W VL VR ζ p.1) p.2
    rw [Sec7.Lemma71D.chartVar, hset, relClosureH_eq hsub hopen]
    exact WangWu.zeroGFFTestCov_neg_neg _ _
  rw [hv, hMp, qF, hc, ← mul_assoc, ← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Ident
end InteractingSLE.Sec5.Lemma47Angle
