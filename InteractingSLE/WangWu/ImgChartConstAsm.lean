/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ImgChartConstRaw

/-!
# The fixed-image-time chart clause: the forward time of an image time, and the right limit

Packet PROVE-WW-B19 (Astra's follow-up note, Part E.4/E.6: "The capacity clock is adapted ... Its inverse takes a
relative stopping time to a stopping time of this original enlarged history"; "Upper dyadic approximations to a
stopping time ... now give (E.4)"). Deterministic and measurability helpers for the optional passage from rational
forward times to a fixed image time `r`:

* `imgTheta s ζ W E r p`: the forward time `θ_r = σ⁻¹(r)` of the image time `r` (`kInv`; `0` after the killing);
  `imgTheta_spec`, `imgTheta_eq_zero`, **`measurable_imgTheta`**;
* `imgAv φ q`: the validity event of the forward-time clause at the forward time `q` (good sample, `q` before contact,
  `supp φ` outside the image hull at `σ(q)` in the chart);
* `chartVar_nonneg`, **`norm_imgF_le_one`**: the explicit characteristic function is bounded by `1`;
* **`tendsto_imgF_dyF`**: along the strict upper dyadic forward times `dyF n θ_r ↓ θ_r`, the validity event holds
  eventually and `imgF(σ(dyF n θ_r)) → imgF(r)` (Lemma 7.1's `tendsto_chart_of_isChartAvoid` along the image times
  `σ(dyF n θ_r) ↓ r`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C (capClock)
open ImgWord LawUnique

namespace ChartConst

/-- **The forward time of the image time `r`**: `σ⁻¹(r)` on the pre-contact times (`0` after the killing). -/
def imgTheta {Ω : Type*} (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1)) (r : ℝ≥0)
    (p : Ω × HistorySpace 1 1) : ℝ≥0 :=
  (kInv (gCurve s ζ W E p) (gPre s ζ W E p) r).toNNReal

/-- **The validity event of the forward-time clause** at the forward time `q`. -/
def imgAv {Ω : Type*} (s : ℚ) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 1 1))
    (φ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) : Set (Ω × HistorySpace 1 1) :=
  {p | p ∈ E ∧ (q : ℝ) ∈ gPre s ζ W E p ∧ Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p)
    (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ (capClock (gCurve s ζ W E p) q).toNNReal}

end ChartConst

open ChartConst

section Theta

variable {Ω : Type*} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

theorem imgTheta_spec (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) {r : ℝ≥0} {p : Ω × HistorySpace 1 1}
    (hr : (r : WithTop ℝ≥0) < imgT s ζ W E p) :
    ((imgTheta s ζ W E r p : ℝ≥0) : ℝ) ∈ gPre s ζ W E p ∧
      capClock (gCurve s ζ W E p) (imgTheta s ζ W E r p) = r := by
  have hγ := isKilledArc_gCurve hs hEg p
  obtain ⟨hm, he⟩ := hγ.kInv_spec hr
  rw [imgTheta, Real.coe_toNNReal _ (hγ.nonneg _ hm)]
  exact ⟨hm, he⟩

theorem imgTheta_eq_zero (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) {r : ℝ≥0} {p : Ω × HistorySpace 1 1}
    (hr : ¬ (r : WithTop ℝ≥0) < imgT s ζ W E p) : imgTheta s ζ W E r p = 0 := by
  classical
  have hγ := isKilledArc_gCurve hs hEg p
  have hne : ¬ ∃ u ∈ gPre s ζ W E p, capClock (gCurve s ζ W E p) u = r := by
    rintro ⟨u, hu, hcu⟩
    have := hγ.lt_kLife hu
    rw [hcu, Real.toNNReal_coe] at this
    exact hr this
  rw [imgTheta, kInv, dite_eq_right_iff.2 (fun h => absurd h hne), Real.toNNReal_zero]

/-- On the alive event, `θ_r < b` iff some rational `q < b` is before contact with `r < σ(q)`. -/
theorem imgTheta_lt_iff (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) {r : ℝ≥0} {p : Ω × HistorySpace 1 1}
    (hr : (r : WithTop ℝ≥0) < imgT s ζ W E p) (b : ℝ≥0) :
    imgTheta s ζ W E r p < b ↔ ∃ q : ℚ, (0 : ℝ) ≤ q ∧ (q : ℝ) < b ∧ (q : ℝ) ∈ gPre s ζ W E p ∧
      (r : ℝ) < capClock (gCurve s ζ W E p) q := by
  have hγ := isKilledArc_gCurve hs hEg p
  obtain ⟨hθP, hθc⟩ := imgTheta_spec hs hEg hr
  constructor
  · intro hlt
    obtain ⟨S', hS'P, hθS'⟩ := hγ.exists_gt _ hθP
    have hlt' : ((imgTheta s ζ W E r p : ℝ≥0) : ℝ) < min (b : ℝ) S' := lt_min (by exact_mod_cast hlt) hθS'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
    have hθ0 : (0 : ℝ) ≤ (imgTheta s ζ W E r p : ℝ≥0) := NNReal.coe_nonneg _
    have hqP : (q : ℝ) ∈ gPre s ζ W E p :=
      hγ.icc S' hS'P ⟨hθ0.trans hq1.le, hq2.le.trans (min_le_right _ _)⟩
    refine ⟨q, hθ0.trans hq1.le, hq2.trans_le (min_le_left _ _), hqP, ?_⟩
    rw [← hθc]
    exact hγ.strictMonoOn_capClock hθP hqP hq1
  · rintro ⟨q, hq0, hqb, hqP, hrq⟩
    have : ((imgTheta s ζ W E r p : ℝ≥0) : ℝ) < q := by
      by_contra hle
      have := hγ.strictMonoOn_capClock.monotoneOn hqP hθP (not_lt.1 hle)
      rw [hθc] at this
      linarith
    exact_mod_cast this.trans hqb

variable [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}

/-- The rational pre-contact events with a capacity bound are measurable. -/
theorem measurableSet_mem_gPre_lt_capClock (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (q : ℚ) (c : ℝ) :
    MeasurableSet {p : Ω × HistorySpace 1 1 | (q : ℝ) ∈ gPre s ζ W E p ∧ c < capClock (gCurve s ζ W E p) q} := by
  have hA := measurableSet_mem_gPre hs hW hE hEg q
  have hc := measurable_indicator_capClock_gCurve hs hW hE hEg q
  have e : {p : Ω × HistorySpace 1 1 | (q : ℝ) ∈ gPre s ζ W E p ∧ c < capClock (gCurve s ζ W E p) q} =
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
theorem measurable_imgTheta (hs : 0 < s) (hW : AdaptedBefore 𝓕 ζ W) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGlueGood s ζ W p) (r : ℝ≥0) : Measurable (imgTheta s ζ W E r) := by
  refine measurable_of_Iio fun b => ?_
  by_cases hb : b = 0
  · subst hb
    have e : imgTheta s ζ W E r ⁻¹' Iio 0 = ∅ := by
      ext p; simp
    rw [e]; exact MeasurableSet.empty
  · have e : imgTheta s ζ W E r ⁻¹' Iio b = {p | ¬ (r : WithTop ℝ≥0) < imgT s ζ W E p} ∪
        ⋃ q : ℚ, ⋃ (_ : (0 : ℝ) ≤ q ∧ (q : ℝ) < b),
          {p | (q : ℝ) ∈ gPre s ζ W E p ∧ (r : ℝ) < capClock (gCurve s ζ W E p) q} := by
      ext p
      simp only [mem_preimage, mem_Iio, mem_union, mem_ofPred_eq, mem_iUnion, exists_prop]
      by_cases hr : (r : WithTop ℝ≥0) < imgT s ζ W E p
      · rw [imgTheta_lt_iff hs hEg hr]
        simp only [hr, not_true_eq_false, false_or]
        constructor
        · rintro ⟨q, h1, h2, h3, h4⟩; exact ⟨q, ⟨h1, h2⟩, h3, h4⟩
        · rintro ⟨q, ⟨h1, h2⟩, h3, h4⟩; exact ⟨q, h1, h2, h3, h4⟩
      · simp only [hr, not_false_eq_true, true_or, iff_true, imgTheta_eq_zero hs hEg hr]
        exact pos_iff_ne_zero.2 hb
    rw [e]
    refine (measurableSet_lt_imgT hs hW hE hEg r).compl.union (MeasurableSet.iUnion fun q =>
      MeasurableSet.iUnion fun _ => measurableSet_mem_gPre_lt_capClock hs hW hE hEg q _)

end Theta

/-! ### The explicit characteristic function is bounded -/

section Bound

variable {Ω : Type*} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

theorem chartVar_nonneg {w : ℝ≥0 → ℝ} {ζ' : ℝ≥0∞} {c : Chart} (hc : c.IsConformal)
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ'}) (φ : TestOn upperHalfPlaneOpens) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < ζ') : 0 ≤ Sec7.Lemma71D.chartVar w c φ q := by
  have hUo := Coupling.MartMeans2.isOpen_H_diff_fwdHull_rpath hw hq
  have hVo : IsOpen (c.2.1 '' (H \ fwdHull (Ito.rpath w) q)) :=
    SmallGammaGeodesics.CC.isOpen_image_conf hUo (hc.1.mono sdiff_subset) (hc.injOn.mono sdiff_subset)
  have hVH : c.2.1 '' (H \ fwdHull (Ito.rpath w) q) ⊆ H := fun z ⟨w', hw', e⟩ => e ▸ hc.2.1 hw'.1
  exact LocalSets.zeroGFFTestCov_self_nonneg hVo hVH φ

/-- **The explicit characteristic function is bounded by `1`** before the killing. -/
theorem norm_imgF_le_one (rL rR : ℝ) (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p)
    (φ : TestOn upperHalfPlaneOpens) {q : ℝ≥0} {p : Ω × HistorySpace 1 1}
    (hq : (q : ℝ≥0∞) < (imgT s ζ W E p : ℝ≥0∞)) : ‖imgF rL rR s ζ W E φ q p‖ ≤ 1 := by
  have hv := chartVar_nonneg (isConformal_imgChart hs p.2) ((isKilledWord_img hs hEg).contW p) φ hq
  rw [imgF, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, sub_zero, zero_sub]
  linarith

end Bound

/-! ### The right limit along strict upper dyadic forward times -/

section Limit

variable {Ω : Type*} {s : ℚ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 1 1)}

/-- **The right limit.** On a good sample where the chart clause is valid at the image time `r`, along the strict
upper dyadic forward times `dyF n θ_r ↓ θ_r` the forward-time validity event holds eventually and
`imgF(σ(dyF n θ_r)) → imgF(r)`. -/
theorem tendsto_imgF_dyF (rL rR : ℝ) (hs : 0 < s) (hEg : ∀ p ∈ E, IsGlueGood s ζ W p)
    {p : Ω × HistorySpace 1 1} (hp : p ∈ E) {r : ℝ≥0} {φ : TestOn upperHalfPlaneOpens}
    (hav : Sec7.Lemma71D.IsChartAvoid (fun t => imgW s ζ W E t p) (imgT s ζ W E p : ℝ≥0∞) (imgChart s p.2) φ r) :
    (∀ᶠ n in atTop, p ∈ imgAv s ζ W E φ (dyF n (imgTheta s ζ W E r p))) ∧
      Tendsto (fun n => imgF rL rR s ζ W E φ
        (capClock (gCurve s ζ W E p) (dyF n (imgTheta s ζ W E r p))).toNNReal p) atTop
        (𝓝 (imgF rL rR s ζ W E φ r p)) := by
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
  obtain ⟨hev, hmean, hvar⟩ := Sec7.Lemma71D.tendsto_chart_of_isChartAvoid (κ := 4) (ρL := imgρ rL)
    (ρR := imgρ rR) (a := 0) (k := 0) (vL := fun i t => imgVL s ζ W E i t p)
    (vR := fun j t => imgVR s ζ W E j t p) (isConformal_imgChart hs p.2) (continuousOn_lift_imgChart p.2)
    (hkw.contW p) (fun i => (hkw.pathL p i).1) (fun j => (hkw.pathR p j).1) hav hsa hts hlim
  refine ⟨?_, ?_⟩
  · obtain ⟨I, hI⟩ := eventually_atTop.1 hev
    refine eventually_atTop.2 ⟨I + N, fun n hn => ?_⟩
    have hnN : n - N + N = n := Nat.sub_add_cancel (le_trans (Nat.le_add_left N I) hn)
    have h := hI (n - N) (by omega)
    simp only [hsi, hnN] at h
    exact ⟨hp, hmemP n (le_trans (Nat.le_add_left N I) hn), h⟩
  · have hF : Tendsto (fun i => imgF rL rR s ζ W E φ (si i) p) atTop (𝓝 (imgF rL rR s ζ W E φ r p)) := by
      simp only [imgF]
      refine (Complex.continuous_exp.tendsto _).comp ?_
      refine (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp hmean)).sub ?_
      exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul hvar)
    exact (tendsto_add_atTop_iff_nat N).1 hF

end Limit

end InteractingSLE.WangWu
