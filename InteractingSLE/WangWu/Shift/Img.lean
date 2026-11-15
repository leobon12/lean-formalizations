/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Shift.Marked
import InteractingSLE.WangWu.ImgChartConstMarks

/-!
# The height-shifted two-slit law, part 6: the two-slit law in the image word's coordinates

Packet PROVE-WW-B26 (PROVE-WW-B19's `ImgChartConstIdent`/`Fwd`/`Raw`/`Asm` with the height shift). B17's image word
`(imgW, imgVL, imgVR)` and B19's chart machinery do not depend on the weights; only the explicit mean does. Here:

* `meanCan_img_eq_chartMeanW`, `ChartConst.imgFW`, `measurable_imgChartAvoid_rawW`, `norm_imgFW_le_one`,
  `tendsto_imgFW_dyF`: B19's R1, explicit characteristic function, R5 measurability, bound and right limit with
  arbitrary weights `ρL ρR : Fin 2 → ℝ` (B19's versions are the weights `![r, −r]`);
* `ae_isGlueGood_shift`: almost every sample of `P ⊗ k(X)` is good;
* **`ae_condExp_twoSlit_glue_eq_imgFW_shift`**: at a rational forward time `t > 0`, almost surely on the good set,
  before contact and when `supp φ` avoids the image hull at `σ(t)` in the chart,
  `E[e^{i(h,φ)} | 𝒜_{A_t ∪ G} ∨ marks] = imgFW ![r_L, −r_L − δ] ![r_R, −r_R + δ] (σ(t))`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open ImgWord LawUnique MartChar.RealFlow

section Img

variable {Ω : Type*} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

/-- **R1 with arbitrary weights: at `κ = 4`, the explicit mean of the image word at `σ(t)` is the chart mean of any
driver of the image hull.** -/
theorem meanCan_img_eq_chartMeanW (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) {p : Ω × HistorySpace 1 1}
    (hp : p ∈ E) {t : ℝ} (ht : t ∈ gPre s ζ W E p) (ht0 : 0 < t) {W' : ℝ → ℝ} (hW' : Continuous W')
    (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') {T : ℝ} (hT : 0 < T)
    (hK : fwdHull W' T = gCurve s ζ W E p '' Ioc 0 t) (ρL ρR : Fin 2 → ℝ) :
    T = capClock (gCurve s ζ W E p) t ∧ ∀ y : ℂ,
      Coupling.meanCan 4 ρL ρR (fun r => imgW s ζ W E r p) (fun i r => imgVL s ζ W E i r p)
        (fun j r => imgVR s ζ W E j r p) T.toNNReal y =
      chartMeanW ρL ρR W' T (frzVL s p.2) (frzVR s p.2) (fwdMap W' T y) := by
  set γ := gCurve s ζ W E p with hγdef
  set P := gPre s ζ W E p with hPdef
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hs hEg p
  obtain ⟨hTc, hEqW⟩ := hγ.eqOn_chainDrv_of_fwdHull_eq ht ht0 hW' hW'0 hη' hη'p hT hK
  refine ⟨hTc, fun y => ?_⟩
  have hT' : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal _ hT.le
  have hlt : ((T.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := by
    have := hγ.lt_kLife ht
    rwa [← hTc] at this
  obtain ⟨-, hkW⟩ := hγ.kW_eq_chainDrv ht
  -- the killed path is `W'` on `[0, T]`
  have hpath : EqOn (kPath γ P) W' (Icc 0 T) := fun r hr => by
    rw [kPath, hkW r (hTc ▸ hr), hEqW hr]
  have hpathn : EqOn (fun r => -kPath γ P r) (fun r => -W' r) (Icc 0 T) := fun r hr => by
    simp only [hpath hr]
  have hWT : imgW s ζ W E T.toNNReal p = W' T := by
    exact hpath ⟨hT.le, le_rfl⟩
  -- the marks at `σ(t)`
  obtain ⟨hgood, hβ, -⟩ := hEg p hp
  obtain ⟨-, -, -, -, -, hvL, hvR⟩ := trace_of_mem_betaSet hs hβ
  have hgXL1 : gXL s E p 1 = -1 / frzVR s p.2 := by simp [gXL, hp]
  have hgXR1 : gXR s E p 1 = -1 / frzVL s p.2 := by simp [gXR, hp]
  have hVL0 : imgVL s ζ W E 0 T.toNNReal p - imgW s ζ W E T.toNNReal p = chartAL W' T := by
    rw [imgVL, kVL_of_lt _ _ hlt, kVLr, kImg_eq hW'.neg hpathn hT'.le, hWT, hT', chartAL]
    simp only [gXL, Matrix.cons_val_zero, neg_zero]
    rfl
  have hVL1 : imgVL s ζ W E 1 T.toNNReal p - imgW s ζ W E T.toNNReal p = chartBL W' T (frzVR s p.2) := by
    rw [imgVL, kVL_of_lt _ _ hlt, kVLr, kImg_eq hW'.neg hpathn hT'.le, hWT, hT', chartBL, hgXL1]
    have hx : -(frzVR s p.2)⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hvR)
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hx.ne hT.le
    rw [← neg_rightImg_neg_sub_eq_re_fwdMap hW' hW'0 hT.le hx hv]
    congr 3
    ring
  have hVR0 : imgVR s ζ W E 0 T.toNNReal p - imgW s ζ W E T.toNNReal p = chartAR W' T := by
    rw [imgVR, kVR_of_lt _ _ hlt, kVRr, kImg_eq hW' hpath hT'.le, hWT, hT', chartAR]
    simp only [gXR, Matrix.cons_val_zero]
  have hVR1 : imgVR s ζ W E 1 T.toNNReal p - imgW s ζ W E T.toNNReal p = chartBR W' T (frzVL s p.2) := by
    rw [imgVR, kVR_of_lt _ _ hlt, kVRr, kImg_eq hW' hpath hT'.le, hWT, hT', chartBR, hgXR1]
    have hx : 0 < -(frzVL s p.2)⁻¹ := neg_pos.2 (inv_lt_zero.2 hvL)
    obtain ⟨v, hv⟩ := exists_isForwardSol_of_isProperArc hη' hη'p hW' hW'0 hx.ne' hT.le
    rw [← rightImg_sub_eq_re_fwdMap hW' hW'0 hT.le hx hv]
    congr 2
    ring
  have hfwd : fwdMap (Ito.rpath fun r => imgW s ζ W E r p) (T.toNNReal : ℝ) y = fwdMap W' T y := by
    rw [hT']
    exact Ito.fwdMap_congr_of_eqOn fun r hr => hpath hr
  rw [Coupling.meanCan, chiC_four, zero_mul, sub_zero, ← condMean_eq_meanHarmonic, hfwd, chartMeanW]
  congr 1
  · funext i
    fin_cases i
    · exact hVL0
    · exact hVL1
  · funext j
    fin_cases j
    · exact hVR0
    · exact hVR1

end Img

namespace ChartConst

/-- **The explicit Gaussian characteristic function of the image word with arbitrary weights** at the image time
`q` (B19's `imgF rL rR` is `imgFW ![rL, −rL] ![rR, −rR]`). -/
def imgFW (ρL ρR : Fin 2 → ℝ) {Ω : Type*} (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (E : Set (Ω × HistorySpace 1 1)) (φ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) (p : Ω × HistorySpace 1 1) : ℂ :=
  Complex.exp (Complex.I * (Sec7.Lemma71D.chartMean 4 ρL ρR (fun r => imgW s ζ W E r p)
      (fun i r => imgVL s ζ W E i r p) (fun j r => imgVR s ζ W E j r p) (imgChart s p.2) 0 0 φ q : ℂ) -
    (((1 / 2 : ℝ) * Sec7.Lemma71D.chartVar (fun r => imgW s ζ W E r p) (imgChart s p.2) φ q : ℝ) : ℂ))

theorem imgF_eq_imgFW (rL rR : ℝ) {Ω : Type*} (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ)
    (E : Set (Ω × HistorySpace 1 1)) : imgF rL rR s ζ W E = imgFW (imgρ rL) (imgρ rR) s ζ W E := rfl

end ChartConst

open ChartConst

section Raw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {s : ℚ} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

/-- **R5's measurability: the chart clause's validity event at a fixed image time is in `imgRaw r`, and so are the
chart mean and the chart variance on it.** -/
theorem measurable_imgChartAvoid_rawW (ρL ρR : Fin 2 → ℝ) (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[imgRaw s ζ W E r] {p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
        (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r} ∧
      Measurable[imgRaw s ζ W E r] ({p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
        (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r}.indicator fun p =>
          Sec7.Lemma71D.chartMean 4 ρL ρR (fun t => imgW s ζ W E t p)
            (fun i t => imgVL s ζ W E i t p) (fun j t => imgVR s ζ W E j t p) (imgChart s p.2) 0 0 φ r) ∧
      Measurable[imgRaw s ζ W E r] ({p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
        (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r}.indicator fun p =>
          Sec7.Lemma71D.chartVar (fun t => imgW s ζ W E t p) (imgChart s p.2) φ r) := by
  have hkw := isKilledWord_img (ζ := ζ) (W := W) hs hEg
  exact Sec7.Lemma71M.measurable_chartAvoid 4 ρL ρR 0 0 (adaptedBefore_imgW_raw hs hW hE hEg)
    (fun p => hkw.contW p) (adaptedBefore_imgVL_raw hs hW hE hEg) (adaptedBefore_imgVR_raw hs hW hE hEg) r
    ((imgRaw s ζ W E).mono (zero_le (a := r))) (fun p => (imgChart s p.2).dom.isOpen)
    (measurableSet_closedBall_subset_dom_imgChart_raw hs) (fun p => isConformal_imgChart hs p.2) (fun _ => rfl)
    (measurable_indicator_fwd_imgChart_raw hs) measurable_indicator_lift_imgChart_raw
    (fun p => continuousOn_lift_imgChart p.2) φ

end Raw

section Bound

variable {Ω : Type*} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

/-- **The explicit characteristic function is bounded by `1`** before the killing. -/
theorem norm_imgFW_le_one (ρL ρR : Fin 2 → ℝ) (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p)
    (φ : TestOn upperHalfPlaneOpens) {q : ℝ≥0} {p : Ω × HistorySpace 1 1}
    (hq : (q : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞)) : ‖imgFW ρL ρR s ζ W E φ q p‖ ≤ 1 := by
  have hv := chartVar_nonneg (isConformal_imgChart hs p.2) ((isKilledWord_img hs hEg).contW p) φ hq
  rw [imgFW, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, sub_zero, zero_sub]
  linarith

end Bound

section Limit

variable {Ω : Type*} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

/-- **The right limit.** On a good sample where the chart clause is valid at the image time `r`, along the strict
upper dyadic forward times `dyF n θ_r ↓ θ_r` the forward-time validity event holds eventually and
`imgF(σ(dyF n θ_r)) → imgF(r)`. -/
theorem tendsto_imgFW_dyF (ρL ρR : Fin 2 → ℝ) (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p)
    {p : Ω × HistorySpace 1 1} (hp : p ∈ E) {r : ℝ≥0} {φ : TestOn upperHalfPlaneOpens}
    (hav : Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p) (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r) :
    (∀ᶠ n in atTop, p ∈ imgAv s ζ W E φ (dyF n (imgTheta s ζ W E r p))) ∧
      Tendsto (fun n => imgFW ρL ρR s ζ W E φ
        (capClock (gCurve s ζ W E p) (dyF n (imgTheta s ζ W E r p))).toNNReal p) atTop
        (𝓝 (imgFW ρL ρR s ζ W E φ r p)) := by
  set γ := gCurve s ζ W E p with hγdef
  set P := gPre s ζ W E p with hPdef
  set θ := imgTheta s ζ W E r p with hθdef
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hs hEg p
  have hkw := isKilledWord_img (ζ := ζ) (W := W) hs hEg
  have hr : (r : WithTop ℝ≥0) < imgT s ζ W E p := hav.1
  obtain ⟨hθP, hθc⟩ := imgTheta_spec hs hEg hr
  obtain ⟨S', hS'P, hθS'⟩ := hγ.exists_gt _ hθP
  have hdyR : Tendsto (fun n => ((dyF n θ : ℝ≥0) : ℝ)) atTop (𝓝 (θ : ℝ)) :=
    (NNReal.continuous_coe.tendsto _).comp (tendsto_dyF θ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hdyR.eventually (gt_mem_nhds hθS'))
  have hmemP : ∀ n ≥ N, ((dyF n θ : ℝ≥0) : ℝ) ∈ P := fun n hn =>
    hγ.icc S' hS'P ⟨NNReal.coe_nonneg _, (hN n hn).le⟩
  set si : ℕ → ℝ≥0 := fun i => (capClock γ (dyF (i + N) θ)).toNNReal with hsi
  have hsa : Antitone si := fun a b hab => Real.toNNReal_le_toNNReal
    (hγ.strictMonoOn_capClock.monotoneOn (hmemP _ (Nat.le_add_left N b)) (hmemP _ (Nat.le_add_left N a))
      (by exact_mod_cast antitone_dyF θ (Nat.add_le_add_right hab N)))
  have hts : ∀ i, r < si i := fun i => by
    have h := hγ.strictMonoOn_capClock hθP (hmemP (i + N) (Nat.le_add_left N i))
      (by exact_mod_cast lt_dyF (i + N) θ)
    rw [hθc] at h
    exact Real.lt_toNNReal_iff_coe_lt.2 h
  have hlim : Tendsto si atTop (𝓝 r) := by
    have hin : Tendsto (fun i => ((dyF (i + N) θ : ℝ≥0) : ℝ)) atTop (𝓝[P] (θ : ℝ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hdyR.comp (tendsto_add_atTop_nat N),
        Eventually.of_forall fun i => hmemP (i + N) (Nat.le_add_left N i)⟩
    have hcap := ((hγ.continuousOn_capClock _ hθP).tendsto).comp hin
    rw [hθc] at hcap
    have h2 := (continuous_real_toNNReal.tendsto _).comp hcap
    rwa [Real.toNNReal_coe] at h2
  obtain ⟨hev, hmean, hvar⟩ := Sec7.Lemma71D.tendsto_chart_of_isChartAvoid (κ := 4) (ρL := ρL)
    (ρR := ρR) (a := 0) (k := 0) (vL := fun i t => imgVL s ζ W E i t p)
    (vR := fun j t => imgVR s ζ W E j t p) (isConformal_imgChart hs p.2) (continuousOn_lift_imgChart p.2)
    (hkw.contW p) (fun i => (hkw.pathL p i).1) (fun j => (hkw.pathR p j).1) hav hsa hts hlim
  refine ⟨?_, ?_⟩
  · obtain ⟨I, hI⟩ := eventually_atTop.1 hev
    refine eventually_atTop.2 ⟨I + N, fun n hn => ?_⟩
    have hnN : n - N + N = n := Nat.sub_add_cancel (le_trans (Nat.le_add_left N I) hn)
    have h := hI (n - N) (by omega)
    simp only [hsi, hnN] at h
    exact ⟨hp, hmemP n (le_trans (Nat.le_add_left N I) hn), h⟩
  · have hF : Tendsto (fun i => imgFW ρL ρR s ζ W E φ (si i) p) atTop (𝓝 (imgFW ρL ρR s ζ W E φ r p)) := by
      simp only [imgFW]
      refine (Complex.continuous_exp.tendsto _).comp ?_
      refine (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp hmean)).sub ?_
      exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul hvar)
    exact (tendsto_add_atTop_iff_nat N).1 hF

end Limit

section Glue

open WholeField LocalSets Coupling

variable {rL rR δ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → DistOn upperHalfPlaneOpens}
  {Ω₂ : Type u} {mΩ₂ : MeasurableSpace Ω₂} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {W₂ : ℝ≥0 → Ω₂ → ℝ} {VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω₂ → ℝ} {B₂ : ℝ≥0 → Ω₂ → ℝ}
  {ζ₂ : Ω₂ → ℝ≥0∞} {h₂ : Ω₂ → DistOn upperHalfPlaneOpens}

/-- **Almost every sample of the shifted glued space is good** (the forward line is a simple proper arc, the reverse
history lies in `BetaSet s` and in `GoodHist s`). -/
theorem ae_isGlueGood_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k) {s : ℚ} (hs : 0 < s) :
    ∀ᵐ p ∂(glueMeasure P k X hXm), IsGlueGood s ζ W p := by
  have hRh₂ : Measurable fun ω => reflectField (h₂ ω) := measurable_reflectField.comp hC₂.2.1
  have hD₂ := measurable_killedHistory hC₂.2.2.2.1
  have hgood := ae_glue_fst (μ := P) k hXm (ae_good_twoSeed hL hR hC.1)
  have hbeta : ∀ᵐ p ∂(glueMeasure P k X hXm), p.2 ∈ BetaSet s :=
    ae_glue_snd hXm hRh₂ hD₂ hlaw k hk (measurableSet_betaSet s) (ae_killedHistory_mem_betaSet hR₁ hL₁ hC₂.1 hs)
  have hgh := ae_goodHist_snd_glueX hL₁ hR₁ hXm hC₂ hlaw k hk s
  filter_upwards [hgood, hbeta, hgh] with p hpα hpβ hpg
  exact ⟨hpα.1, hpβ, hpg⟩

/-- **R1 on the glued space.** At a rational forward time `t > 0`, almost surely on the good set, before contact and
when `supp φ` avoids the image hull at `σ(t)` in the chart `Ψ`, the conditional characteristic function of `(h, φ)`
given the germ of the two stopped slits and both stopped histories is `imgF(σ(t))`. -/
theorem ae_condExp_twoSlit_glue_eq_imgFW_shift (hL : 0 ≤ rL) (hR : 0 ≤ rR) (hL₁ : 0 ≤ rL + δ) (hR₁ : 0 ≤ rR - δ)
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h)
    {X : Ω → DistOn upperHalfPlaneOpens} (hXm : Measurable X)
    (hX : ∀ ω, h ω = Exist.flowField 0 (δ * wwLambda) (X ω))
    (hC₂ : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rR - δ) (fun _ => rL + δ) P₂ 𝓕₂ W₂ VL₂ VR₂
      B₂ ζ₂ h₂)
    (hlaw : P.map X = P₂.map (fun ω => reflectField (h₂ ω)))
    (k : Kernel (DistOn upperHalfPlaneOpens) (HistorySpace 1 1)) [IsMarkovKernel k]
    (hk : P₂.map (fun ω => (reflectField (h₂ ω), killedHistory W₂ VL₂ VR₂ ζ₂ ω)) =
      P₂.map (fun ω => reflectField (h₂ ω)) ⊗ₘ k)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    {t s : ℚ} (ht : 0 < t) (hs : 0 < s) (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ p ∂(glueMeasure P k X hXm), p ∈ glueGood (glueMeasure P k X hXm) s ζ W →
      (t : ℝ) ∈ gPre s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p →
      Sec7.Lemma71D.IsChartAvoid (fun r => imgW s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) r p)
        (imgT s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p : ℝ≥0∞) (imgChart s p.2) φ
        (capClock (gCurve s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p) t).toNNReal →
      (glueMeasure P k X hXm)[fun p' => Complex.exp (Complex.I * (h p'.1 φ : ℂ)) |
          germSigma (fun p : Ω × HistorySpace 1 1 =>
            histHull t (killedHistory W VL VR ζ p.1) ∪ negInv '' histHull s p.2) (fun p => centredField h u₀ p.1) ⊔
            twoSlitMarks W VL VR ζ t s] p =
        imgFW ![rL, -rL - δ] ![rR, -rR + δ] s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) φ
          (capClock (gCurve s ζ W (glueGood (glueMeasure P k X hXm) s ζ W) p) t).toNNReal p := by
  set μ := glueMeasure P k X hXm with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGlueGood s ζ W p := fun p hp => isGlueGood_of_mem_glueGood p hp
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hs' : (0 : ℝ) ≤ s := by exact_mod_cast hs.le
  filter_upwards [ae_condExp_cexp_twoSlit_glue_shift hL hR hL₁ hR₁ hC hXm hX hC₂ hlaw k hk hu₀ ht hs φ,
    ae_glue_fst (μ := P) k hXm (ae_histHull_eq_image_seedLine hL hR hC ht)] with p hB hA hpE htP havoid
  obtain ⟨hα, hβ, -⟩ := hEg p hpE
  obtain ⟨hWβc, hWβ0, -, -, hGeq, -, -⟩ := trace_of_mem_betaSet hs hβ
  set A := histHull t (killedHistory W VL VR ζ p.1) with hAdef
  set Wβ := Ito.rpath (frzDrive s p.2) with hWβdef
  have hP : gPre s ζ W E p = preContact (seedLine ζ W p.1) (negInv '' histHull s p.2) := gPre_of_mem hpE
  have hγ : gCurve s ζ W E p = imgCurve Wβ s (seedLine ζ W p.1) := gCurve_of_mem hpE
  have htP' := hP ▸ htP
  have hAsub : A ⊆ H \ negInv '' fwdHull Wβ s := by
    rw [hA, ← hGeq]
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨hα.mem_H u hu.1, htP'.2 u ⟨hu.1.le, hu.2⟩⟩
  have hdisj : Disjoint A (negInv '' histHull s p.2) := by
    rw [hGeq]
    exact Set.disjoint_left.2 fun z hz hzG => (hAsub hz).2 hzG
  have hγimg : gCurve s ζ W E p '' Ioc 0 t = revChart Wβ s '' A := by
    rw [hγ, hA, image_image]
    refine image_congr fun u hu => ?_
    simp only [imgCurve, not_le.2 hu.1, ↓reduceIte]
  have hkill : IsKilledArc (gCurve s ζ W E p) (gPre s ζ W E p) := isKilledArc_gCurve hs hEg p
  have hcap0 : 0 ≤ capClock (gCurve s ζ W E p) t := hkill.capClock_nonneg htP
  have hhull : fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) t).toNNReal : ℝ≥0) : ℝ) = revChart Wβ s '' A := by
    rw [Real.coe_toNNReal _ hcap0, ← hγimg]
    exact hkill.fwdHull_eq_of_eqOn_chainDrv (fun S hS r hr => (hkill.kW_eq_chainDrv hS).2 r hr) htP
  have hset : (imgChart s p.2).2.1 '' (H \ fwdHull (Ito.rpath fun r => imgW s ζ W E r p)
      (((capClock (gCurve s ζ W E p) t).toNNReal : ℝ≥0) : ℝ)) = H \ (A ∪ negInv '' histHull s p.2) := by
    simp only [imgChart]
    rw [revDrv0_of_mem hs hβ, hhull, revChartInv_image_H_diff hWβc hWβ0 hs' hAsub, hGeq]
  have hsupp : tsupport φ ⊆ H \ (A ∪ negInv '' histHull s p.2) := hset ▸ havoid.2
  obtain ⟨W', hW'c, hW'0, T, hT, η', hη', hη'p, hK', hval⟩ := hB hdisj hsupp
  have hK : fwdHull W' T = gCurve s ζ W E p '' Ioc 0 t := hK'.trans hγimg.symm
  obtain ⟨hTc, hmean⟩ := meanCan_img_eq_chartMeanW hs hEg hpE htP ht0 hW'c hW'0 hη' hη'p hT hK
    ![rL, -rL - δ] ![rR, -rR + δ]
  rw [hval, imgFW, ← hTc]
  have hm : Sec7.Lemma71D.chartMean 4 ![rL, -rL - δ] ![rR, -rR + δ] (fun r => imgW s ζ W E r p)
      (fun i r => imgVL s ζ W E i r p) (fun j r => imgVR s ζ W E j r p) (imgChart s p.2) 0 0 φ T.toNNReal =
      ∫ z, chartMeanW ![rL, -rL - δ] ![rR, -rR + δ] W' T (frzVL s p.2) (frzVR s p.2)
        (fwdMap W' T (revChart Wβ s z)) * φ z := by
    rw [Sec7.Lemma71D.chartMean]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [imgChart, sub_zero, zero_mul]
    rw [revDrv0_of_mem hs hβ, hmean]
  have hv : Sec7.Lemma71D.chartVar (fun r => imgW s ζ W E r p) (imgChart s p.2) φ T.toNNReal =
      QuantumZipper.zeroGFFTestCov (H \ (A ∪ negInv '' histHull s p.2)) φ φ := by
    rw [Sec7.Lemma71D.chartVar, hTc, hset]
  rw [hm, hv, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Glue

end InteractingSLE.WangWu
