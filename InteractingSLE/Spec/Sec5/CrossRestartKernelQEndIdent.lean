/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndCong

/-!
# Lemma 4.7 in the chart `Q`: the conditional mean as the chart mean of the killed image word, and step R1

Packet PROVE-CFRESTART5, items D2 (mean bridge) and D3 (first step). On the glued space of `Prop411Q.CfGlueAE`, at a
flow time `s > 0` and a counterflow time `t > 0`, almost surely on the validity event `qAv φ t` (a good sample, `t`
before contact, `supp φ` inside the remaining chart domain at the image time `σ(t)`):

* **`ae_condExp_glue_eq_neg_chartMean`** (the Lemma 4.7 form of GLUECOND7's `MeanIdent49Statement`, proved): the
  conditional mean of the centred field given the germ of `A_s ∪ G_t` and both stopped histories, plus `∫ 𝔥₀ φ`, is
  minus the chart mean of the killed image word (parameter `16/κ`, weights `slitRhoL/R ρ′ κ (π/2)`) at `σ(t)`, in the
  chart `fChart = R ∘ f_s` with height shift `−πχ/2` and lift coefficient `−χ = χ(16/κ)`. Proof: PROVE-CFRESTART3's
  `ae_condExp_cfGlue_eq_imgChart47` for the image setup of a frozen driver of the killed word
  (`exists_isCfImgSetup_q`) and the mean bridge `meanCan_q_eq`;
* **`ae_condExp_glue_eq_qF`** (step R1): the conditional characteristic function of `(−h, φ)` given the same
  σ-algebra is the explicit `qF(σ(t))` (chart mean and chart variance of the image word).

The image coordinates of `−h` are those of a counterflow-parameter field (`k = χ(16/κ) = −χ`, ruling R57's companion
for the reversed direction): the chart clause is stated for the field `−h`.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar.RealFlow WholeField LocalSets CrossCond

namespace Kill47

/-! ### The image word's weights and the explicit characteristic function -/

section Def

variable {Ω : Type*} {nL nR mL mR : ℕ}

/-- **The left weights of the counterflow's image word** (the counterflow word at `16/κ` and the junction weight at the
relative angle `π/2`). -/
abbrev iwL (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :=
  CrossRestart.slitRhoL (qρL κ ρL ρR xL xR) κ (π / 2)

/-- **The right weights of the counterflow's image word.** -/
abbrev iwR (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) :=
  CrossRestart.slitRhoR (qρR κ ρL ρR xL xR) κ (π / 2)

/-- **The explicit Gaussian characteristic function of the image word at the image time `r`**: the chart mean (height
shift `aC`, lift coefficient `kC`) and the chart variance of `fChart` along the killed image word. -/
def qF (a : ℝ) (ρL' : Fin (mL + 1) → ℝ) (ρR' : Fin (mR + 1) → ℝ) (xL' : Fin mL → ℝ) (xR' : Fin mR → ℝ)
    (aC kC : ℝ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
    (s : ℝ≥0) (E : Set (Ω × HistorySpace 0 0)) (φ : TestOn upperHalfPlaneOpens) (r : ℝ≥0)
    (p : Ω × HistorySpace 0 0) : ℂ :=
  Complex.exp (Complex.I * (Sec7.Lemma71D.chartMean a ρL' ρR' (fun t => qW W VL VR ζ s E t p)
      (fun i t => qVL xL' W VL VR ζ s E i t p) (fun j t => qVR xR' W VL VR ζ s E j t p) (fChart W VL VR ζ s p)
      aC kC φ r : ℂ) -
    (((1 / 2 : ℝ) * Sec7.Lemma71D.chartVar (fun t => qW W VL VR ζ s E t p) (fChart W VL VR ζ s p) φ r : ℝ) : ℂ))

/-- **The counterflow time of the image time `r`**: `σ⁻¹(r)` before the killing (`0` after). -/
def qTheta (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)
    (E : Set (Ω × HistorySpace 0 0)) (r : ℝ≥0) (p : Ω × HistorySpace 0 0) : ℝ≥0 :=
  (kcInv (qgCurve W s E p) (qgPre W VL VR ζ s E p) r).toNNReal

/-- **The validity event at the counterflow time `t`**: a good sample, `t` before contact, and `supp φ` inside the
remaining chart domain at the image time `σ(t)`. -/
def qAv (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)
    (E : Set (Ω × HistorySpace 0 0)) (φ : TestOn upperHalfPlaneOpens) (t : ℝ≥0) : Set (Ω × HistorySpace 0 0) :=
  {p | p ∈ E ∧ (t : ℝ) ∈ qgPre W VL VR ζ s E p ∧ Sec7.Lemma71D.IsChartAvoid (fun r => qW W VL VR ζ s E r p)
    (qT W VL VR ζ s E p : ℝ≥0∞) (fChart W VL VR ζ s p) φ (capClock (qgCurve W s E p) t).toNNReal}

end Def

/-! ### The mean identification -/

section Ident

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {_mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {h₂ : Ω₂ → DistOn upperHalfPlaneOpens} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞}

/-- **The conditional mean given both stopped histories is minus the chart mean of the killed image word** (Lemma 4.7
direction of G3 (ii); item D2). -/
theorem ae_condExp_glue_eq_neg_chartMean (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {s : ℝ≥0} (hs : 0 < s) {t : ℝ≥0} (ht : 0 < t) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      p ∈ qAv W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) φ t →
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
          fun p' => cenT κ u₀ (cfField κ (h p'.1)) φ |
          germSigma (fun p : Ω × HistorySpace 0 0 => hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
            (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ s t] p +
          ∫ z, u₀ z * φ z =
        -Sec7.Lemma71D.chartMean (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
          (fun r => qW W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) r p)
          (fun i r => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k
            (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) i r p)
          (fun j r => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s (glueGood47 (glueMeasure P k
            (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) j r p)
          (fChart W VL VR ζ s p) (-(π / 2 * chiC κ)) (-chiC κ) φ
          (capClock (qgCurve W s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p) t).toNNReal := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood47 μ W VL VR ζ with hEdef
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 ht
  filter_upwards [ae_condExp_cfGlue_eq_imgChart47 hκ hκ4 hF h44 hC hcf hlaw k hk hu₀ s t hs φ] with p hcfr hAv
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
  obtain ⟨u, hu⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ) (iwL κ ρL ρR xL xR)
    (iwR κ ρL ρR xL xR)
    (fun i => -rightImg (fun r => -W' r) (-GlueImg.imgMarkL (qxL κ ρL ρR xL xR) Wf s i) T - W' T)
    (fun j => rightImg W' (GlueImg.imgMarkR (qxR κ ρL ρR xL xR) Wf s j) T - W' T)
  have hid := hcfr hφ W' η' T hset u hu
  rw [hid, Sec7.Lemma71D.chartMean, ← integral_neg]
  have hmL : ∀ i, -rightImg (fun r => -W' r) (-GlueImg.imgMarkL (qxL κ ρL ρR xL xR) Wf s i) T - W' T ≤ 0 :=
    fun i => by
      have := le_rightImg (show Continuous fun r => -W' r from hset.hW'.neg)
        (-GlueImg.imgMarkL (qxL κ ρL ρR xL xR) Wf s i) hT0.le
      linarith
  have hmR : ∀ j, 0 ≤ rightImg W' (GlueImg.imgMarkR (qxR κ ρL ρR xL xR) Wf s j) T - W' T := fun j => by
    have := le_rightImg hset.hW' (GlueImg.imgMarkR (qxR κ ρL ρR xL xR) Wf s j) hT0.le
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
  show (_ : ℝ) * φ z = -((Coupling.meanCan (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
      (fun r => qW W VL VR ζ s E r p) (fun i r => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E i r p)
      (fun j r => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E j r p) T.toNNReal ((fChart W VL VR ζ s p).1 z) -
      -(π / 2 * chiC κ) - -chiC κ * (fChart W VL VR ζ s p).2.2 z) * φ z)
  rw [fChart_fst_eq hg, fChart_lift_eq hg hzC.1, meanCan_q_eq hpE hT0.le hTc.le hlt hset.hW' hEq,
    ← Ito.eqOn_meanHarmonic hmL hmR hu hfH, Sec4.chiC_sixteen_div hκ]
  simp only [hWf]
  unfold fDrv
  ring

/-- **Step R1 (Lemma 4.7 direction).** At a counterflow time `t > 0`, almost surely on the validity event, the
conditional characteristic function of `(−h, φ)` given the germ of `A_s ∪ G_t` and both stopped histories is the
explicit `qF(σ(t))`. -/
theorem ae_condExp_glue_eq_qF (hκ : 0 < κ) (hκ4 : κ < 4) (hF : IsOrderedForceWord xL xR)
    (h44 : Sec4.Cond44 κ ρL ρR) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hcf : IsCenteredCounterflowDriver κ P₂ h₂ W₂ ζ₂) (hlaw : P.map (fun ω => cfField κ (h ω)) = P₂.map h₂)
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 0 0)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (h₂ ω, cfHistory W₂ ζ₂ ω)) = P₂.map h₂ ⊗ₘ k) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {s : ℝ≥0} (hs : 0 < s) {t : ℝ≥0} (ht : 0 < t) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1)),
      p ∈ qAv W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
        ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) φ t →
      (glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1))[
          fun p' => Complex.exp (Complex.I * ((-(h p'.1 φ) : ℝ) : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 0 0 => hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2)
            (fun p => cenT κ u₀ (cfField κ (h p.1))) ⊔ cfGlueMarks W VL VR ζ s t] p =
        qF (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR) (qxL κ ρL ρR xL xR) (qxR κ ρL ρR xL xR)
          (-(π / 2 * chiC κ)) (-chiC κ) W VL VR ζ s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) φ
          (capClock (qgCurve W s (glueGood47 (glueMeasure P k (fun ω => cfField κ (h ω))
            ((measurable_cfField κ).comp hC.2.1)) W VL VR ζ) p) t).toNNReal p := by
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood47 μ W VL VR ζ with hEdef
  have hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p := isGood47_of_mem_glueGood47
  set U : Ω × HistorySpace 0 0 → Set ℂ := fun p => hullAt s (killedHistory W VL VR ζ p.1) ∪ cfHullQ t p.2
    with hUdef
  set F : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => cenT κ u₀ (cfField κ (h p.1)) with hFdef
  have hX := hC.2.2.2.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hFg := isZeroBoundaryGFF_cenT_glue (k := k) hC hu₀
  have hAm : Measurable[_, hittingSigma] U :=
    measurable_union_hitting (((measurable_hullAt s).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ t).comp measurable_snd)
  have hAae := CrossCond.Word49.ae_hullAt_eq_image_seedLine hκ hκ4 hF h44 hC
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hAae] with ω hω using hω.1
  have hreg₂ := CrossCond.Word49.ae_cfReg hκ hκ4 hF h44 hC hcf hlaw
  have hmark := isHistoryAvoidanceLocal_cfGlue hC hκ hζ hcf hreg₂ hlaw hk hu₀ s t
  have hℋ := cfGlueMarks_le (Ω := Ω) s t hX
  obtain ⟨M, -, hM1, hM2⟩ := exists_condExp_germSigma_history hFg hAm hℋ hmark
    (Eventually.of_forall fun p => union_relClosed s t _ p.2) (-φ)
  set c : ℂ := Complex.exp (Complex.I * ((-∫ z, u₀ z * φ z : ℝ) : ℂ)) with hc
  have hFφ : ∀ p : Ω × HistorySpace 0 0, F p φ = h p.1 φ - ∫ z, u₀ z * φ z := fun p => by
    simp only [hFdef, cenT_cfField]
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
  have hid := ae_condExp_glue_eq_neg_chartMean hκ hκ4 hF h44 hC hcf hlaw k hk hu₀ hs ht φ
  filter_upwards [hM1, hM2, hpull, hid, hneg] with p h1 h2 h5 h4 h6 hAv
  obtain ⟨hpE, htP, hav⟩ := hAv
  have hset := fChart_inv_image_eq hEg hpE htP
  rw [h5, Pi.smul_apply, ← h2, smul_eq_mul]
  have hMp : M p = Sec7.Lemma71D.chartMean (16 / κ) (iwL κ ρL ρR xL xR) (iwR κ ρL ρR xL xR)
      (fun r => qW W VL VR ζ s E r p) (fun i r => qVL (qxL κ ρL ρR xL xR) W VL VR ζ s E i r p)
      (fun j r => qVR (qxR κ ρL ρR xL xR) W VL VR ζ s E j r p) (fChart W VL VR ζ s p) (-(π / 2 * chiC κ))
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

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
