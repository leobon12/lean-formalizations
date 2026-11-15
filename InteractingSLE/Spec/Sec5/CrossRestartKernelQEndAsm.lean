/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelQEndIdent
import InteractingSLE.Spec.Sec5.CrossCondMartAsm

/-!
# Lemma 4.7 in the chart `Q`: the counterflow time of an image time, right limits, and raw measurability

Packet PROVE-CFRESTART5, item D3 (the Lemma 4.7 mirror of GLUECOND7's `CrossCondMartAsm`, for the non-simple killed
image word of PROVE-CFRESTART4):

* `qTheta s r`: the counterflow time `σ⁻¹(r)` of the image time `r` (`qTheta_spec`, `qTheta_lt_iff`,
  **`measurable_qTheta`**);
* `norm_qF_le_one`: the explicit characteristic function is bounded by `1` before the killing;
* **`tendsto_qF_dyF`**: along the strict upper dyadic counterflow times `dyF n θ_r ↓ θ_r` the validity event holds
  eventually and `qF(σ(dyF n θ_r)) → qF(r)` (right continuity, Astra's E.4);
* **`measurable_fChartAvoid_raw`**: at a fixed image time `r`, the validity event of the chart clause, the chart mean
  and the chart variance on it are known at time `r` of the raw image filtration `qRaw` (the chart is read from the
  stopped flow history, time-`0` information).

Generic in the image word's parameter, weights and marks (`a`, `ρL'`, `ρR'`, ordered marks `xL'`, `xR'`).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart.KernelQ

open Sec7.Lemma71C (capClock)
open WangWu hiding ratPt exists_ratPt_dist_lt
open LawUnique GlueCond Cond44Ref CfRegQ Prop411Q MartChar
open WangWu.ChartConst (dyq dyIdx dyF lt_dyF antitone_dyF tendsto_dyF dyIdx_eq_iff)

namespace Kill47

/-! ### The counterflow time of an image time -/

section Theta

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}

theorem qTheta_spec (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) {r : ℝ≥0} {p : Ω × HistorySpace 0 0}
    (hr : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p) :
    ((qTheta W VL VR ζ s E r p : ℝ≥0) : ℝ) ∈ qgPre W VL VR ζ s E p ∧
      capClock (qgCurve W s E p) (qTheta W VL VR ζ s E r p) = r := by
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  obtain ⟨hm, he⟩ := hγ.kcInv_spec hr
  rw [qTheta, Real.coe_toNNReal _ (hγ.nonneg _ hm)]
  exact ⟨hm, he⟩

/-- On the alive event, `θ_r < b` iff some rational `q < b` is before contact with `r < σ(q)`. -/
theorem qTheta_lt_iff (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) {r : ℝ≥0} {p : Ω × HistorySpace 0 0}
    (hr : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p) (b : ℝ≥0) :
    qTheta W VL VR ζ s E r p < b ↔ ∃ q : ℚ, (0 : ℝ) ≤ q ∧ (q : ℝ) < b ∧ (q : ℝ) ∈ qgPre W VL VR ζ s E p ∧
      (r : ℝ) < capClock (qgCurve W s E p) q := by
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  obtain ⟨hθP, hθc⟩ := qTheta_spec hEg hr
  constructor
  · intro hlt
    obtain ⟨S', hS'P, hθS'⟩ := hγ.exists_gt _ hθP
    have hlt' : ((qTheta W VL VR ζ s E r p : ℝ≥0) : ℝ) < min (b : ℝ) S' := lt_min (by exact_mod_cast hlt) hθS'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt'
    have hθ0 : (0 : ℝ) ≤ (qTheta W VL VR ζ s E r p : ℝ≥0) := NNReal.coe_nonneg _
    have hqP : (q : ℝ) ∈ qgPre W VL VR ζ s E p :=
      hγ.icc S' hS'P ⟨hθ0.trans hq1.le, hq2.le.trans (min_le_right _ _)⟩
    refine ⟨q, hθ0.trans hq1.le, hq2.trans_le (min_le_left _ _), hqP, ?_⟩
    rw [← hθc]
    exact hγ.strictMonoOn_capClock hθP hqP hq1
  · rintro ⟨q, hq0, hqb, hqP, hrq⟩
    have : ((qTheta W VL VR ζ s E r p : ℝ≥0) : ℝ) < q := by
      by_contra hle
      have := hγ.strictMonoOn_capClock.monotoneOn hqP hθP (not_lt.1 hle)
      rw [hθc] at this
      linarith
    exact_mod_cast this.trans hqb

theorem qTheta_eq_zero (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) {r : ℝ≥0} {p : Ω × HistorySpace 0 0}
    (hr : ¬ (r : WithTop ℝ≥0) < qT W VL VR ζ s E p) : qTheta W VL VR ζ s E r p = 0 := by
  classical
  have hγ := isKilledCurve_qgCurve (q := s) hEg p
  have hne : ¬ ∃ u, 0 ≤ u ∧ capClock (kcCurve (qgCurve W s E p) (qgPre W VL VR ζ s E p)) u = r := by
    rintro ⟨u, hu0, hu⟩
    refine hr ?_
    show (r : WithTop ℝ≥0) < kcLife (qgCurve W s E p) (qgPre W VL VR ζ s E p)
    rw [lt_kcLife_iff_ofReal, ← hu]
    exact hγ.isDrivenCurve.ofReal_capClock_lt hu0
  rw [qTheta, kcInv, Sec7.Lemma71C.capInv, dite_eq_right_iff.2 (fun h => absurd h hne), kcTime_zero, Real.toNNReal_zero]

variable [mΩ : MeasurableSpace Ω]

/-- The rational pre-contact events with a capacity bound are measurable. -/
theorem measurableSet_mem_qgPre_lt_capClock (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (q : ℚ) (c : ℝ) :
    MeasurableSet {p : Ω × HistorySpace 0 0 | (q : ℝ) ∈ qgPre W VL VR ζ s E p ∧
      c < capClock (qgCurve W s E p) q} := by
  have hA := measurableSet_mem_qgPre (q := s) hX hE hEg q
  have hc := measurable_indicator_capClock_qgCurve (q := s) hX hE hEg q
  have e : {p : Ω × HistorySpace 0 0 | (q : ℝ) ∈ qgPre W VL VR ζ s E p ∧ c < capClock (qgCurve W s E p) q} =
      {p | (q : ℝ) ∈ qgPre W VL VR ζ s E p} ∩ {p | c < ({p | (q : ℝ) ∈ qgPre W VL VR ζ s E p}.indicator
        (fun p => capClock (qgCurve W s E p) q) p)} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [indicator_of_mem (show p ∈ {p | (q : ℝ) ∈ qgPre W VL VR ζ s E p} from h1)]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rwa [indicator_of_mem (show p ∈ {p | (q : ℝ) ∈ qgPre W VL VR ζ s E p} from h1)] at h2⟩
  rw [e]
  exact hA.inter (measurableSet_lt measurable_const hc)

/-- **The counterflow time of the image time `r` is measurable.** -/
theorem measurable_qTheta (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (r : ℝ≥0) : Measurable (qTheta W VL VR ζ s E r) := by
  refine measurable_of_Iio fun b => ?_
  by_cases hb : b = 0
  · subst hb
    have e : qTheta W VL VR ζ s E r ⁻¹' Iio 0 = ∅ := by
      ext p; simp
    rw [e]; exact MeasurableSet.empty
  · have e : qTheta W VL VR ζ s E r ⁻¹' Iio b = {p | ¬ (r : WithTop ℝ≥0) < qT W VL VR ζ s E p} ∪
        ⋃ q : ℚ, ⋃ (_ : (0 : ℝ) ≤ q ∧ (q : ℝ) < b),
          {p | (q : ℝ) ∈ qgPre W VL VR ζ s E p ∧ (r : ℝ) < capClock (qgCurve W s E p) q} := by
      ext p
      simp only [mem_preimage, mem_Iio, mem_union, mem_ofPred_eq, mem_iUnion, exists_prop]
      by_cases hr : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p
      · rw [qTheta_lt_iff hEg hr]
        simp only [hr, not_true_eq_false, false_or]
        constructor
        · rintro ⟨q, h1, h2, h3, h4⟩; exact ⟨q, ⟨h1, h2⟩, h3, h4⟩
        · rintro ⟨q, ⟨h1, h2⟩, h3, h4⟩; exact ⟨q, h1, h2, h3, h4⟩
      · simp only [hr, not_false_eq_true, true_or, iff_true, qTheta_eq_zero hEg hr]
        exact pos_iff_ne_zero.2 hb
    rw [e]
    refine (measurableSet_lt_qT hX hE hEg r).compl.union (MeasurableSet.iUnion fun q =>
      MeasurableSet.iUnion fun _ => measurableSet_mem_qgPre_lt_capClock hX hE hEg q _)

end Theta

/-! ### The explicit characteristic function is bounded -/

section Bound

variable {Ω : Type*} {nL nR mL mR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)} {a : ℝ}
  {ρL' : Fin (mL + 1) → ℝ} {ρR' : Fin (mR + 1) → ℝ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {aC kC : ℝ}

/-- The killed image word of ordered marks is a killed word. -/
theorem isKilledWord_q_of_ordered (hxo : IsOrderedForceWord xL' xR') (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p)
    (hs : 0 < s) :
    WangWu.ImgDrv.IsKilledWord (qW W VL VR ζ s E) (qVL xL' W VL VR ζ s E) (qVR xR' W VL VR ζ s E)
      (qT W VL VR ζ s E) :=
  isKilledWord_q hxo.2.1 hxo.1 hxo.2.2.2 hxo.2.2.1 hEg hs

/-- **The explicit characteristic function is bounded by `1`** before the killing. -/
theorem norm_qF_le_one (hxo : IsOrderedForceWord xL' xR') (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hs : 0 < s)
    (φ : TestOn upperHalfPlaneOpens) {r : ℝ≥0} {p : Ω × HistorySpace 0 0}
    (hr : (r : ℝ≥0∞) < (qT W VL VR ζ s E p : ℝ≥0∞)) :
    ‖qF a ρL' ρR' xL' xR' aC kC W VL VR ζ s E φ r p‖ ≤ 1 := by
  have hv := CrossCond.Word49.chartVar_nonneg_of_conformal (isConformal_fChart (W := W) (VL := VL) (VR := VR)
    (ζ := ζ) (s := s) p) ((isKilledWord_q_of_ordered hxo hEg hs).contW p) φ hr
  rw [qF, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, sub_zero, zero_sub]
  linarith

end Bound

/-! ### The right limit along strict upper dyadic counterflow times -/

section Limit

variable {Ω : Type*} {nL nR mL mR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)} {a : ℝ}
  {ρL' : Fin (mL + 1) → ℝ} {ρR' : Fin (mR + 1) → ℝ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ} {aC kC : ℝ}

/-- **The right limit.** On a good sample where the chart clause is valid at the image time `r`, along the strict
upper dyadic counterflow times `dyF n θ_r ↓ θ_r` the validity event holds eventually and
`qF(σ(dyF n θ_r)) → qF(r)`. -/
theorem tendsto_qF_dyF (hxo : IsOrderedForceWord xL' xR') (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hs : 0 < s)
    {p : Ω × HistorySpace 0 0} (hp : p ∈ E) {r : ℝ≥0} {φ : TestOn upperHalfPlaneOpens}
    (hav : Sec7.Lemma71D.IsChartAvoid (fun t => qW W VL VR ζ s E t p) (qT W VL VR ζ s E p : ℝ≥0∞)
      (fChart W VL VR ζ s p) φ r) :
    (∀ᶠ n in atTop, p ∈ qAv W VL VR ζ s E φ (dyF n (qTheta W VL VR ζ s E r p))) ∧
      Tendsto (fun n => qF a ρL' ρR' xL' xR' aC kC W VL VR ζ s E φ
        (capClock (qgCurve W s E p) (dyF n (qTheta W VL VR ζ s E r p))).toNNReal p) atTop
        (𝓝 (qF a ρL' ρR' xL' xR' aC kC W VL VR ζ s E φ r p)) := by
  set γ := qgCurve W s E p with hγdef
  set P := qgPre W VL VR ζ s E p with hPdef
  set θ := qTheta W VL VR ζ s E r p with hθdef
  have hγ : IsKilledCurve γ P := isKilledCurve_qgCurve hEg p
  have hkw := isKilledWord_q_of_ordered hxo hEg hs
  have hr : (r : WithTop ℝ≥0) < qT W VL VR ζ s E p := hav.1
  obtain ⟨hθP, hθc⟩ := qTheta_spec hEg hr
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
  obtain ⟨hev, hmean, hvar⟩ := Sec7.Lemma71D.tendsto_chart_of_isChartAvoid (κ := a) (ρL := ρL')
    (ρR := ρR') (a := aC) (k := kC) (vL := fun i t => qVL xL' W VL VR ζ s E i t p)
    (vR := fun j t => qVR xR' W VL VR ζ s E j t p) (isConformal_fChart p) (continuousOn_lift_fChart p)
    (hkw.contW p) (fun i => (hkw.pathL p i).1) (fun j => (hkw.pathR p j).1) hav hsa hts hlim
  refine ⟨?_, ?_⟩
  · obtain ⟨I, hI⟩ := eventually_atTop.1 hev
    refine eventually_atTop.2 ⟨I + N, fun n hn => ?_⟩
    have hnN : n - N + N = n := Nat.sub_add_cancel (le_trans (Nat.le_add_left N I) hn)
    have h := hI (n - N) (by omega)
    simp only [hsi, hnN] at h
    exact ⟨hp, hmemP n (le_trans (Nat.le_add_left N I) hn), h⟩
  · have hF' : Tendsto (fun i => qF a ρL' ρR' xL' xR' aC kC W VL VR ζ s E φ (si i) p) atTop
        (𝓝 (qF a ρL' ρR' xL' xR' aC kC W VL VR ζ s E φ r p)) := by
      simp only [qF]
      refine (Complex.continuous_exp.tendsto _).comp ?_
      refine (tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp hmean)).sub ?_
      exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul hvar)
    exact (tendsto_add_atTop_iff_nat N).1 hF'

end Limit

/-! ### The candidate is known at the image time of the raw filtration -/

section Raw

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR mL mR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {s : ℝ≥0}
  {E : Set (Ω × HistorySpace 0 0)} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}

theorem adaptedBefore_qW_raw (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) :
    AdaptedBefore (qRaw xL' xR' W VL VR ζ s E) (fun p => (qT W VL VR ζ s E p : ℝ≥0∞)) (qW W VL VR ζ s E) := by
  intro t A hA
  have e : {p : Ω × HistorySpace 0 0 | (t : ℝ≥0∞) < (qT W VL VR ζ s E p : ℝ≥0∞) ∧ qW W VL VR ζ s E t p ∈ A} =
      {p | (t : WithTop ℝ≥0) < qT W VL VR ζ s E p} ∩ qW W VL VR ζ s E t ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_qRaw_of_gen ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩ (measurableSet_lt_qT hX hE hEg t)).inter
    (measurableSet_qRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inl rfl⟩⟩ (measurable_qW hX hE hEg t hA))

theorem adaptedBefore_qVL_raw (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (i : Fin (mL + 1)) :
    AdaptedBefore (qRaw xL' xR' W VL VR ζ s E) (fun p => (qT W VL VR ζ s E p : ℝ≥0∞))
      (qVL xL' W VL VR ζ s E i) := by
  intro t A hA
  have e : {p : Ω × HistorySpace 0 0 | (t : ℝ≥0∞) < (qT W VL VR ζ s E p : ℝ≥0∞) ∧
      qVL xL' W VL VR ζ s E i t p ∈ A} =
      {p | (t : WithTop ℝ≥0) < qT W VL VR ζ s E p} ∩ qVL xL' W VL VR ζ s E i t ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_qRaw_of_gen ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩ (measurableSet_lt_qT hX hE hEg t)).inter
    (measurableSet_qRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inr (Or.inl ⟨i, rfl⟩)⟩⟩
      (measurable_qVL xL' hX hE hEg i t hA))

theorem adaptedBefore_qVR_raw (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (j : Fin (mR + 1)) :
    AdaptedBefore (qRaw xL' xR' W VL VR ζ s E) (fun p => (qT W VL VR ζ s E p : ℝ≥0∞))
      (qVR xR' W VL VR ζ s E j) := by
  intro t A hA
  have e : {p : Ω × HistorySpace 0 0 | (t : ℝ≥0∞) < (qT W VL VR ζ s E p : ℝ≥0∞) ∧
      qVR xR' W VL VR ζ s E j t p ∈ A} =
      {p | (t : WithTop ℝ≥0) < qT W VL VR ζ s E p} ∩ qVR xR' W VL VR ζ s E j t ⁻¹' A := rfl
  rw [e]
  exact (measurableSet_qRaw_of_gen ⟨t, le_rfl, Or.inr (Or.inl rfl)⟩ (measurableSet_lt_qT hX hE hEg t)).inter
    (measurableSet_qRaw_of_gen ⟨t, le_rfl, Or.inl ⟨A, hA, Or.inr (Or.inr ⟨j, rfl⟩)⟩⟩
      (measurable_qVR xR' hX hE hEg j t hA))

/-- **The chart clause's validity event at a fixed image time is in `qRaw r`, and so are the chart mean and the chart
variance on it.** -/
theorem measurable_fChartAvoid_raw (a : ℝ) (ρL' : Fin (mL + 1) → ℝ) (ρR' : Fin (mR + 1) → ℝ) (aC kC : ℝ)
    (hxo : IsOrderedForceWord xL' xR') (hX : IsMeasurableKilledDriving W VL VR ζ) (hE : MeasurableSet E)
    (hEg : ∀ p ∈ E, IsGood47 W VL VR ζ p) (hs : 0 < s) (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) :
    MeasurableSet[qRaw xL' xR' W VL VR ζ s E r] {p | Sec7.Lemma71D.IsChartAvoid (fun t => qW W VL VR ζ s E t p)
        (qT W VL VR ζ s E p : ℝ≥0∞) (fChart W VL VR ζ s p) φ r} ∧
      Measurable[qRaw xL' xR' W VL VR ζ s E r] ({p | Sec7.Lemma71D.IsChartAvoid
        (fun t => qW W VL VR ζ s E t p) (qT W VL VR ζ s E p : ℝ≥0∞) (fChart W VL VR ζ s p) φ r}.indicator fun p =>
          Sec7.Lemma71D.chartMean a ρL' ρR' (fun t => qW W VL VR ζ s E t p)
            (fun i t => qVL xL' W VL VR ζ s E i t p) (fun j t => qVR xR' W VL VR ζ s E j t p)
            (fChart W VL VR ζ s p) aC kC φ r) ∧
      Measurable[qRaw xL' xR' W VL VR ζ s E r] ({p | Sec7.Lemma71D.IsChartAvoid
        (fun t => qW W VL VR ζ s E t p) (qT W VL VR ζ s E p : ℝ≥0∞) (fChart W VL VR ζ s p) φ r}.indicator fun p =>
          Sec7.Lemma71D.chartVar (fun t => qW W VL VR ζ s E t p) (fChart W VL VR ζ s p) φ r) := by
  have hkw := isKilledWord_q_of_ordered hxo hEg hs
  have hY := measurable_flowStop_qRaw (xL := xL') (xR := xR') (E := E) (s := s) hX 0
  exact Sec7.Lemma71M.measurable_chartAvoid a ρL' ρR' aC kC (adaptedBefore_qW_raw hX hE hEg)
    (fun p => hkw.contW p) (adaptedBefore_qVL_raw hX hE hEg) (adaptedBefore_qVR_raw hX hE hEg) r
    ((qRaw xL' xR' W VL VR ζ s E).mono (zero_le (a := r))) (fun p => (fChart W VL VR ζ s p).dom.isOpen)
    (fun z ρ => measurableSet_closedBall_subset_dom_fChart_of hY z ρ) (fun p => isConformal_fChart p) (fun _ => rfl)
    (fun z => measurable_indicator_fwd_fChart_of hY z) (fun z => measurable_indicator_lift_fChart_of hY z)
    (fun p => continuousOn_lift_fChart p) φ

end Raw

end Kill47

end InteractingSLE.Sec5.CrossRestart.KernelQ
