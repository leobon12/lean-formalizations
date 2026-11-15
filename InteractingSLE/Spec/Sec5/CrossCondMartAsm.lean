/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondMart
import InteractingSLE.WangWu.ImgChartConstDyadic
import InteractingSLE.Spec.Sec7.Lemma71MMeas

/-!
# The chart clause at fixed image times (general `κ`): the explicit characteristic function, the forward time of an
image time, right limits, and the measurability of the candidate

Packet PROVE-GLUECOND7. The general-`κ` form of PROVE-WW-B19's assembly (`WangWu/ImgChartConstAsm`,
`ImgChartConstRaw`) for the image word of `Word49` (the flow line given the counterflow prefix, in the counterflow
chart `cfChart s y = (Ψ, Ψ⁻¹, Im L_Ψ)`, lift coefficient `χ`, height shift `2πχ`):

* `cfF`: the explicit Gaussian characteristic function at the image time `q` (chart mean and chart variance of the
  image word); `norm_cfF_le_one`;
* `cfTheta s ζ W E r`: the forward time `σ⁻¹(r)` of the image time `r` (measurable: `measurable_cfTheta`), and the
  forward validity events `cfAv`;
* **`tendsto_cfF_dyF`**: along the strict upper dyadic forward times `dyF n θ_r ↓ θ_r` the validity event holds
  eventually and `cfF(σ(dyF n θ_r)) → cfF(r)` (Astra's E.4, right continuity);
* **`measurable_cfChartAvoid_raw`**: the validity event of the chart clause at a fixed image time, the chart mean and
  the chart variance on it are known at that image time of the raw image filtration.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q
open ImgDrv MartChar
open Sec7.Lemma71C (capClock)
open WangWu.ChartConst (dyq dyIdx dyF lt_dyF antitone_dyF tendsto_dyF dyIdx_eq_iff)

namespace Word49

/-! ### Definitions -/

section Def

variable {Ω : Type*} {nL nR : ℕ}

/-- **The explicit Gaussian characteristic function of the image word at the image time `q`**: the chart mean (lift
coefficient `χ`, height shift `2πχ`) and the chart variance of `cfChart` along the killed image word. -/
def cfF (cL cR : ℝ → ℝ → ℝ) (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (s : ℝ≥0)
    (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (φ : TestOn upperHalfPlaneOpens) (q : ℝ≥0)
    (p : Ω × HistorySpace 0 0) : ℂ :=
  Complex.exp (Complex.I * (Sec7.Lemma71D.chartMean κ (jwL cL κ ρL) (jwR cR κ ρR) (fun r => imgW s ζ W E r p)
      (fun i r => imgVL xL s ζ W E i r p) (fun j r => imgVR xR s ζ W E j r p) (cfChart s p.2)
      (2 * Real.pi * chiC κ) (chiC κ) φ q : ℂ) -
    (((1 / 2 : ℝ) * Sec7.Lemma71D.chartVar (fun r => imgW s ζ W E r p) (cfChart s p.2) φ q : ℝ) : ℂ))

/-- **The forward time of the image time `r`**: `σ⁻¹(r)` on the pre-contact times (`0` after the killing). -/
def cfTheta (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (r : ℝ≥0)
    (p : Ω × HistorySpace 0 0) : ℝ≥0 :=
  (kInv (gCurve s ζ W E p) (gPre s ζ W E p) r).toNNReal

/-- **The validity event of the forward-time clause** at the forward time `q`. -/
def cfAv (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (φ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) : Set (Ω × HistorySpace 0 0) :=
  {p | p ∈ E ∧ (q : ℝ) ∈ gPre s ζ W E p ∧ Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
    (imgT s ζ W E p : ℝ≥0∞) (cfChart s p.2) φ (capClock (gCurve s ζ W E p) q).toNNReal}

end Def

/-! ### The forward time of an image time -/

section Theta

variable {Ω : Type*} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}

theorem cfTheta_spec (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {r : ℝ≥0} {p : Ω × HistorySpace 0 0}
    (hr : (r : WithTop ℝ≥0) < imgT s ζ W E p) :
    ((cfTheta s ζ W E r p : ℝ≥0) : ℝ) ∈ gPre s ζ W E p ∧ capClock (gCurve s ζ W E p) (cfTheta s ζ W E r p) = r := by
  have hγ := isKilledArc_gCurve hEg p
  obtain ⟨hm, he⟩ := hγ.kInv_spec hr
  rw [cfTheta, Real.coe_toNNReal _ (hγ.nonneg _ hm)]
  exact ⟨hm, he⟩

theorem cfTheta_eq_zero (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {r : ℝ≥0} {p : Ω × HistorySpace 0 0}
    (hr : ¬ (r : WithTop ℝ≥0) < imgT s ζ W E p) : cfTheta s ζ W E r p = 0 := by
  classical
  have hγ := isKilledArc_gCurve hEg p
  have hne : ¬ ∃ u ∈ gPre s ζ W E p, capClock (gCurve s ζ W E p) u = r := by
    rintro ⟨u, hu, hcu⟩
    have := hγ.lt_kLife hu
    rw [hcu, Real.toNNReal_coe] at this
    exact hr this
  rw [cfTheta, kInv, dite_eq_right_iff.2 (fun h => absurd h hne), Real.toNNReal_zero]

/-- On the alive event, `θ_r < b` iff some rational `q < b` is before contact with `r < σ(q)`. -/
theorem cfTheta_lt_iff (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {r : ℝ≥0} {p : Ω × HistorySpace 0 0}
    (hr : (r : WithTop ℝ≥0) < imgT s ζ W E p) (b : ℝ≥0) :
    cfTheta s ζ W E r p < b ↔ ∃ q : ℚ, (0 : ℝ) ≤ q ∧ (q : ℝ) < b ∧ (q : ℝ) ∈ gPre s ζ W E p ∧
      (r : ℝ) < capClock (gCurve s ζ W E p) q := by
  have hγ := isKilledArc_gCurve hEg p
  obtain ⟨hθP, hθc⟩ := cfTheta_spec hEg hr
  constructor
  · intro hlt
    obtain ⟨S', hS'P, hθS'⟩ := hγ.exists_gt _ hθP
    have hlt' : ((cfTheta s ζ W E r p : ℝ≥0) : ℝ) < min (b : ℝ) S' := lt_min (by exact_mod_cast hlt) hθS'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
    have hθ0 : (0 : ℝ) ≤ (cfTheta s ζ W E r p : ℝ≥0) := NNReal.coe_nonneg _
    have hqP : (q : ℝ) ∈ gPre s ζ W E p :=
      hγ.icc S' hS'P ⟨hθ0.trans hq1.le, hq2.le.trans (min_le_right _ _)⟩
    refine ⟨q, hθ0.trans hq1.le, hq2.trans_le (min_le_left _ _), hqP, ?_⟩
    rw [← hθc]
    exact hγ.strictMonoOn_capClock hθP hqP hq1
  · rintro ⟨q, hq0, hqb, hqP, hrq⟩
    have : ((cfTheta s ζ W E r p : ℝ≥0) : ℝ) < q := by
      by_contra hle
      have := hγ.strictMonoOn_capClock.monotoneOn hqP hθP (not_lt.1 hle)
      rw [hθc] at this
      linarith
    exact_mod_cast this.trans hqb

variable [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}

/-- The rational pre-contact events with a capacity bound are measurable. -/
theorem measurableSet_mem_gPre_lt_capClock (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (q : ℚ) (c : ℝ) :
    MeasurableSet {p : Ω × HistorySpace 0 0 | (q : ℝ) ∈ gPre s ζ W E p ∧ c < capClock (gCurve s ζ W E p) q} := by
  have hA := measurableSet_mem_gPre hW hE hEg q
  have hc := measurable_indicator_capClock_gCurve hW hE hEg q
  have e : {p : Ω × HistorySpace 0 0 | (q : ℝ) ∈ gPre s ζ W E p ∧ c < capClock (gCurve s ζ W E p) q} =
      {p | (q : ℝ) ∈ gPre s ζ W E p} ∩ {p | c < ({p | (q : ℝ) ∈ gPre s ζ W E p}.indicator
        (fun p => capClock (gCurve s ζ W E p) q) p)} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [indicator_of_mem (show p ∈ {p | (q : ℝ) ∈ gPre s ζ W E p} from h1)]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [indicator_of_mem (show p ∈ {p | (q : ℝ) ∈ gPre s ζ W E p} from h1)] at h2⟩
  rw [e]
  exact hA.inter (measurableSet_lt measurable_const hc)

/-- **The forward time of the image time `r` is measurable.** -/
theorem measurable_cfTheta (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    (r : ℝ≥0) : Measurable (cfTheta s ζ W E r) := by
  refine measurable_of_Iio fun b => ?_
  by_cases hb : b = 0
  · subst hb
    have e : cfTheta s ζ W E r ⁻¹' Iio 0 = ∅ := by
      ext p; simp
    rw [e]; exact MeasurableSet.empty
  · have e : cfTheta s ζ W E r ⁻¹' Iio b = {p | ¬ (r : WithTop ℝ≥0) < imgT s ζ W E p} ∪
        ⋃ q : ℚ, ⋃ (_ : (0 : ℝ) ≤ q ∧ (q : ℝ) < b),
          {p | (q : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) q} := by
      ext p
      simp only [mem_preimage, mem_Iio, mem_union, mem_ofPred_eq, mem_iUnion, exists_prop]
      by_cases hr : (r : WithTop ℝ≥0) < imgT s ζ W E p
      · rw [cfTheta_lt_iff hEg hr]
        simp only [hr, not_true_eq_false, false_or]
        constructor
        · rintro ⟨q, h1, h2, h3, h4⟩; exact ⟨q, ⟨h1, h2⟩, h3, h4⟩
        · rintro ⟨q, ⟨h1, h2⟩, h3, h4⟩; exact ⟨q, h1, h2, h3, h4⟩
      · simp only [hr, not_false_eq_true, true_or, iff_true, cfTheta_eq_zero hEg hr]
        exact pos_iff_ne_zero.2 hb
    rw [e]
    refine (measurableSet_lt_imgT hW hE hEg r).compl.union (MeasurableSet.iUnion fun q =>
      MeasurableSet.iUnion fun _ => measurableSet_mem_gPre_lt_capClock hW hE hEg q _)

end Theta

/-! ### The explicit characteristic function is bounded -/

section Bound

variable {Ω : Type*} {nL nR : ℕ} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {cL cR : ℝ → ℝ → ℝ}

/-- The chart variance is nonnegative before the killing (an adapter of `LocalSets.zeroGFFTestCov_self_nonneg`). -/
theorem chartVar_nonneg_of_conformal {w : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {c : Chart} (hc : c.IsConformal)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ'}) (φ : TestOn upperHalfPlaneOpens) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < ζ') : 0 ≤ Sec7.Lemma71D.chartVar w c φ q := by
  have hUo := Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath hw hq
  have hVo : IsOpen (c.2.1 '' (H \ fwdHull (Ito.rpath w) q)) :=
    SmallGammaGeodesics.CC.isOpen_image_conf hUo (hc.1.mono sdiff_subset) (hc.injOn.mono sdiff_subset)
  have hVH : c.2.1 '' (H \ fwdHull (Ito.rpath w) q) ⊆ H := fun z ⟨w', hw', e⟩ => e ▸ hc.2.1 hw'.1
  exact LocalSets.zeroGFFTestCov_self_nonneg hVo hVH φ

/-- **The explicit characteristic function is bounded by `1`** before the killing. -/
theorem norm_cfF_le_one (hF : IsOrderedForceWord xL xR) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    (φ : TestOn upperHalfPlaneOpens) {q : ℝ≥0} {p : Ω × HistorySpace 0 0}
    (hq : (q : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞)) : ‖cfF cL cR κ ρL ρR xL xR s ζ W E φ q p‖ ≤ 1 := by
  have hv := chartVar_nonneg_of_conformal (isConformal_cfChart (s := s) p.2) ((isKilledWord_img hF hEg).contW p) φ hq
  rw [cfF, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, sub_zero, zero_sub]
  linarith

end Bound

/-! ### The right limit along strict upper dyadic forward times -/

section Limit

variable {Ω : Type*} {nL nR : ℕ} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {cL cR : ℝ → ℝ → ℝ}

/-- **The right limit.** On a good sample where the chart clause is valid at the image time `r`, along the strict
upper dyadic forward times `dyF n θ_r ↓ θ_r` the forward-time validity event holds eventually and
`cfF(σ(dyF n θ_r)) → cfF(r)`. -/
theorem tendsto_cfF_dyF (hF : IsOrderedForceWord xL xR) (hEg : ∀ p ∈ E, IsGood49 s ζ W p)
    {p : Ω × HistorySpace 0 0} (hp : p ∈ E) {r : ℝ≥0} {φ : TestOn upperHalfPlaneOpens}
    (hav : Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p) (imgT s ζ W E p : ℝ≥0∞) (cfChart s p.2) φ r) :
    (∀ᶠ n in atTop, p ∈ cfAv s ζ W E φ (dyF n (cfTheta s ζ W E r p))) ∧
      Tendsto (fun n => cfF cL cR κ ρL ρR xL xR s ζ W E φ
        (capClock (gCurve s ζ W E p) (dyF n (cfTheta s ζ W E r p))).toNNReal p) atTop
        (𝓝 (cfF cL cR κ ρL ρR xL xR s ζ W E φ r p)) := by
  set γ := gCurve s ζ W E p with hγdef
  set P := gPre s ζ W E p with hPdef
  set θ := cfTheta s ζ W E r p with hθdef
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hEg p
  have hkw := isKilledWord_img (ζ := ζ) (W := W) hF hEg
  have hr : (r : WithTop ℝ≥0) < imgT s ζ W E p := hav.1
  obtain ⟨hθP, hθc⟩ := cfTheta_spec hEg hr
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
  obtain ⟨hev, hmean, hvar⟩ := Sec7.Lemma71D.tendsto_chart_of_isChartAvoid (κ := κ) (ρL := jwL cL κ ρL)
    (ρR := jwR cR κ ρR) (a := 2 * Real.pi * chiC κ) (k := chiC κ) (vL := fun i t => imgVL xL s ζ W E i t p)
    (vR := fun j t => imgVR xR s ζ W E j t p) (isConformal_cfChart p.2) (continuousOn_lift_cfChart p.2)
    (hkw.contW p) (fun i => (hkw.pathL p i).1) (fun j => (hkw.pathR p j).1) hav hsa hts hlim
  refine ⟨?_, ?_⟩
  · obtain ⟨I, hI⟩ := eventually_atTop.1 hev
    refine eventually_atTop.2 ⟨I + N, fun n hn => ?_⟩
    have hnN : n - N + N = n := Nat.sub_add_cancel (le_trans (Nat.le_add_left N I) hn)
    have h := hI (n - N) (by omega)
    simp only [hsi, hnN] at h
    exact ⟨hp, hmemP n (le_trans (Nat.le_add_left N I) hn), h⟩
  · have hF' : Tendsto (fun i => cfF cL cR κ ρL ρR xL xR s ζ W E φ (si i) p) atTop
        (𝓝 (cfF cL cR κ ρL ρR xL xR s ζ W E φ r p)) := by
      simp only [cfF]
      refine (Complex.continuous_exp.tendsto _).comp ?_
      refine (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp hmean)).sub ?_
      exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul hvar)
    exact (tendsto_add_atTop_iff_nat N).1 hF'

end Limit

/-! ### The candidate is known at the image time of the raw filtration -/

section RawChart

variable {s : ℝ≥0}

theorem adaptedBefore_cfProc : AdaptedBefore (stopFilt s) (fun _ => (⊤ : ℝ≥0∞)) (cfProc s) := by
  intro t A hA
  have e : {y : HistorySpace 0 0 | (t : ℝ≥0∞) < ⊤ ∧ cfProc s t y ∈ A} = cfProc s t ⁻¹' A := by
    ext y
    simp only [mem_ofPred_eq, mem_preimage, ENNReal.coe_lt_top, true_and]
  rw [e]
  exact adapted_cfProc t hA

/-- **The closed-ball domain events of the chart are known from the stopped history.** -/
theorem measurableSet_closedBall_subset_dom_cfChart (z : ℂ) (ρ : ℝ) :
    MeasurableSet[stopSigma s] {y : HistorySpace 0 0 | closedBall z ρ ⊆ ((cfChart s y).dom : Set ℂ)} := by
  classical
  by_cases hB : closedBall z ρ ⊆ H
  · have hQ : IsCompact (negInv '' closedBall z ρ) := by
      refine (isCompact_closedBall z ρ).image_of_continuousOn fun w hw => ?_
      exact (continuousAt_negInv (ne_zero_of_mem_H (hB hw))).continuousWithinAt
    have hc : ∀ y : HistorySpace 0 0, ContinuousOn (fun t => cfProc s t y)
        {t : ℝ≥0 | (t : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) y} := fun y => (continuous_cfProc y).continuousOn
    have h := Sec7.Lemma71M.measurableSet_lt_subset_H_diff_fwdHull adaptedBefore_cfProc hc s hQ
    have e : {y : HistorySpace 0 0 | closedBall z ρ ⊆ ((cfChart s y).dom : Set ℂ)} =
        {y | (s : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) y ∧ negInv '' closedBall z ρ ⊆
          H \ fwdHull (fun t : ℝ => cfProc s t.toNNReal y) (s : ℝ)} := by
      ext y
      have hrp : (fun t : ℝ => cfProc s t.toNNReal y) = cfDrv0 s y := rpath_cfProc y
      simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, hrp]
      constructor
      · rintro hsub _ ⟨w, hw, rfl⟩
        obtain ⟨hwH, hwK⟩ := (mem_dom_cfChart_iff y).1 (hsub hw)
        exact ⟨Sec7.StripSysField.negInv_mem_H hwH, hwK⟩
      · intro hsub w hw
        exact (mem_dom_cfChart_iff y).2 ⟨hB hw, (hsub ⟨w, hw, rfl⟩).2⟩
    rw [e]
    exact h
  · have e : {y : HistorySpace 0 0 | closedBall z ρ ⊆ ((cfChart s y).dom : Set ℂ)} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro hsub
      exact hB fun w hw => ((mem_dom_cfChart_iff y).1 (hsub hw)).1
    rw [e]
    exact @MeasurableSet.empty _ (stopSigma s)

end RawChart

section Raw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞}
  {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- The counterflow history stopped at `s` is known at every time of the raw image filtration. -/
theorem measurable_cfStop_imgRaw (r : ℝ≥0) :
    Measurable[imgRaw xL xR s ζ W E r] fun p : Ω × HistorySpace 0 0 => cfStop s p.2 := fun B hB =>
  measurableSet_imgRaw_of_gen ⟨0, zero_le, Or.inr (Or.inr (Or.inr ⟨B, hB, rfl⟩))⟩
    ((measurable_cfStop s).comp measurable_snd hB)

theorem adaptedBefore_imgW_raw (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) :
    AdaptedBefore (imgRaw xL xR s ζ W E) (fun p => (imgT s ζ W E p : ℝ≥0∞)) (imgW s ζ W E) := by
  intro t A hA
  have e : {p : Ω × HistorySpace 0 0 | (t : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) ∧ imgW s ζ W E t p ∈ A} =
      {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} ∩ imgW s ζ W E t ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩ (measurableSet_lt_imgT hW hE hEg t)).inter
    (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inl rfl⟩⟩ (measurable_imgW hW hE hEg t hA))

theorem adaptedBefore_imgVL_raw (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (i : Fin (nL + 1)) :
    AdaptedBefore (imgRaw xL xR s ζ W E) (fun p => (imgT s ζ W E p : ℝ≥0∞)) (imgVL xL s ζ W E i) := by
  intro t A hA
  have e : {p : Ω × HistorySpace 0 0 | (t : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) ∧ imgVL xL s ζ W E i t p ∈ A} =
      {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} ∩ imgVL xL s ζ W E i t ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩ (measurableSet_lt_imgT hW hE hEg t)).inter
    (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩
      (measurable_imgVL xL hW hE hEg i t hA))

theorem adaptedBefore_imgVR_raw (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (j : Fin (nR + 1)) :
    AdaptedBefore (imgRaw xL xR s ζ W E) (fun p => (imgT s ζ W E p : ℝ≥0∞)) (imgVR xR s ζ W E j) := by
  intro t A hA
  have e : {p : Ω × HistorySpace 0 0 | (t : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞) ∧ imgVR xR s ζ W E j t p ∈ A} =
      {p | (t : WithTop ℝ≥0) < imgT s ζ W E p} ∩ imgVR xR s ζ W E j t ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩ (measurableSet_lt_imgT hW hE hEg t)).inter
    (measurableSet_imgRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inr (Or.inr ⟨j, rfl⟩)⟩⟩
      (measurable_imgVR xR hW hE hEg j t hA))

/-- **The chart clause's validity event at a fixed image time is in `imgRaw r`, and so are the chart mean and the
chart variance on it.** -/
theorem measurable_cfChartAvoid_raw (cL cR : ℝ → ℝ → ℝ) (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hF : IsOrderedForceWord xL xR)
    (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E) (hEg : ∀ p ∈ E, IsGood49 s ζ W p) (r : ℝ≥0)
    (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[imgRaw xL xR s ζ W E r] {p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
        (imgT s ζ W E p : ℝ≥0∞) (cfChart s p.2) φ r} ∧
      Measurable[imgRaw xL xR s ζ W E r] ({p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
        (imgT s ζ W E p : ℝ≥0∞) (cfChart s p.2) φ r}.indicator fun p =>
          Sec7.Lemma71D.chartMean κ (jwL cL κ ρL) (jwR cR κ ρR) (fun t => imgW s ζ W E t p)
            (fun i t => imgVL xL s ζ W E i t p) (fun j t => imgVR xR s ζ W E j t p) (cfChart s p.2)
            (2 * Real.pi * chiC κ) (chiC κ) φ r) ∧
      Measurable[imgRaw xL xR s ζ W E r] ({p | Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
        (imgT s ζ W E p : ℝ≥0∞) (cfChart s p.2) φ r}.indicator fun p =>
          Sec7.Lemma71D.chartVar (fun t => imgW s ζ W E t p) (cfChart s p.2) φ r) := by
  have hkw := isKilledWord_img (ζ := ζ) (W := W) hF hEg
  have hY := measurable_cfStop_imgRaw (xL := xL) (xR := xR) (s := s) (ζ := ζ) (W := W) (E := E) 0
  exact Sec7.Lemma71M.measurable_chartAvoid κ (jwL cL κ ρL) (jwR cR κ ρR) (2 * Real.pi * chiC κ) (chiC κ)
    (adaptedBefore_imgW_raw hW hE hEg) (fun p => hkw.contW p) (adaptedBefore_imgVL_raw hW hE hEg)
    (adaptedBefore_imgVR_raw hW hE hEg) r ((imgRaw xL xR s ζ W E).mono (zero_le (a := r)))
    (fun p => (cfChart s p.2).dom.isOpen)
    (fun z ρ => measurableSet_comp_of_stopSigma (Y := Prod.snd) (measurableSet_closedBall_subset_dom_cfChart z ρ) hY)
    (fun p => isConformal_cfChart p.2) (fun _ => rfl)
    (fun z => measurable_indicator_fwd_cfChart_comp (Y := Prod.snd) hY z)
    (fun z => measurable_indicator_lift_cfChart_comp (Y := Prod.snd) hY z)
    (fun p => continuousOn_lift_cfChart p.2) φ

end Raw

end Word49

end InteractingSLE.Sec5.CrossCond
