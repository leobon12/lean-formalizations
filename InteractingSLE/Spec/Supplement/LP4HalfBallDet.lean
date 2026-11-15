import InteractingSLE.Spec.ZhanGT4.Collar
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowBoundary
import InteractingSLE.Spec.Sec4.Aux25Real
import InteractingSLE.Spec.Supplement.LP3Flow
import InteractingSLE.Spec.Sec7.TwoForceMain3Transfer

/-!
# LP4's collar step: the deterministic part

Packet PROVE-LP17. Specification p. 482–483 (proof of Proposition LP4, second paragraph): "On `E_T`, let `f_T` be
the inverse hydrodynamic map. Finite trace continuity gives its continuous extension to the spherical closed
half-plane. … its preimage fiber `F = f_T^{-1}({0})` is a compact subset of the open real interval
`(V_T^L, V_T^R)` … Apply LP3 … Apply Zhan's independent ordinary-SLE result [Zha10, Corollary 6.1] … every real
point strictly between the swallowed real extremes has a relative upper-half-plane neighborhood inside the swallowed
hull. … By compactness and continuity of `f_T` on the spherical closure, its physical image is bounded away from `0`."

The fiber is handled through a **cluster condition** in the style of [RS05, Lemma 7.3]
(`Foundations/SLE/SpaceFilling/Swallow.lean`): at the restart time `σ`, every `z ∈ ℍ \ K_σ` near `0` has
`Re f_σ(z)` in a compact interval `[m₁, m₂]` strictly inside the force interval `(V^L_σ − W_σ, V^R_σ − W_σ)`.

## Main results

* `halfBall_of_cluster_of_collar`: **the pull-back.** If the cluster condition holds at `t₁` with `[m₁, m₂]`, and
  the restarted driver swallows real points `p₁ < m₁`, `p₂ > m₂` by time `s` and has the real collar at `s`
  (`ZhanGT4.HasRealCollar`), then `K_{t₁ + s}` contains a half-ball around `0`. (`Im f_{t₁}(z) ≤ Im z` replaces
  the continuity of `f_T` at the fiber.)
* `exists_cluster_bounds`: **the fiber lies inside the force interval.** If real points `y₁ < 0 < y₂` are
  swallowed by `σ` and every real `c` beyond the force coordinates is the image of a real point alive at `σ` on the
  corresponding side (`Aux25.exists_isForwardSol_of_gt`), the cluster condition holds with `ℓ < m₁ ≤ m₂ < r`.
* `hasRealCollar_congr`: the collar at `s` reads the driver on `[0, s]` only.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper QuantumZipper.RS

namespace InteractingSLE.LP.LP4HB

/-! ### Congruence of the collar -/

theorem isSwallowedBy_congr {W W' : ℝ → ℝ} {s : ℝ} (h : ∀ r ∈ Icc (0 : ℝ) s, W r = W' r) {x : ℝ}
    (hx : ZhanGT4.IsSwallowedBy W x s) : ZhanGT4.IsSwallowedBy W' x s := fun ⟨v, hv⟩ =>
  hx ⟨v, QuantumZipper.isForwardSol_congr_drive (fun r hr => (h r hr).symm) hv⟩

/-- **The collar at `s` reads the driver on `[0, s]` only.** -/
theorem hasRealCollar_congr {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') {s : ℝ} (hs : 0 ≤ s)
    (h : ∀ r ∈ Icc (0 : ℝ) s, W r = W' r) (hcol : ZhanGT4.HasRealCollar W s) :
    ZhanGT4.HasRealCollar W' s := by
  intro x y z hx hz hxy hyz
  have h' : ∀ r ∈ Icc (0 : ℝ) s, W' r = W r := fun r hr => (h r hr).symm
  obtain ⟨ε, hε, hball⟩ := hcol x y z (isSwallowedBy_congr h' hx) (isSwallowedBy_congr h' hz) hxy hyz
  have hK : fwdHull W s = fwdHull W' s := YuanCorollary13.fwdHull_eq_of_eqOn_Icc hW hW' hs h
  exact ⟨ε, hε, fun w hw hwy => hK ▸ hball w hw hwy⟩

/-! ### The pull-back -/

/-- `Im f_t(z) ≤ Im z` off the hull. -/
theorem im_fwdMap_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ H \ fwdHull W t) : (fwdMap W t z).im ≤ z.im := by
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull ht hz.1 hz.2
  rw [fwdMap_eq hW hz.1 hu ⟨ht, le_rfl⟩]
  have hmono := (im_isForwardSol_le hW hz.1 hu).1
  have h0 : u 0 = z := by
    have h := (hu.2 0 ⟨le_rfl, ht⟩).2
    simpa [hW0] using h
  have := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only at this
  rwa [h0] at this

/-- **The pull-back of the collar.** If the cluster condition holds at `t₁` with `[m₁, m₂]`, and the restarted
driver has swallowed `p₁ < m₁` and `p₂ > m₂` by time `s` and has the real collar at `s`, then `K_{t₁ + s}`
contains a half-ball around `0`. -/
theorem halfBall_of_cluster_of_collar {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {t₁ s : ℝ}
    (ht₁ : 0 ≤ t₁) (hs : 0 ≤ s) {ε m₁ m₂ p₁ p₂ : ℝ} (hε : 0 < ε) (hp₁ : p₁ < m₁) (hp₂ : m₂ < p₂)
    (hcl : ∀ z ∈ H \ fwdHull W t₁, ‖z‖ < ε → m₁ ≤ (fwdMap W t₁ z).re ∧ (fwdMap W t₁ z).re ≤ m₂)
    (hsw₁ : ZhanGT4.IsSwallowedBy (shiftDrive W t₁) p₁ s)
    (hsw₂ : ZhanGT4.IsSwallowedBy (shiftDrive W t₁) p₂ s)
    (hcol : ZhanGT4.HasRealCollar (shiftDrive W t₁) s) :
    ∃ ε' > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε' → z ∈ fwdHull W (t₁ + s) := by
  set V := shiftDrive W t₁ with hV
  -- a collar radius at every point of `[m₁, m₂]`
  have hrad : ∀ y : Icc m₁ m₂, ∃ e > (0 : ℝ), ∀ w ∈ H, ‖w - (y : ℝ)‖ < e → w ∈ fwdHull V s := fun y =>
    hcol p₁ y p₂ hsw₁ hsw₂ (hp₁.trans_le y.2.1) (y.2.2.trans_lt hp₂)
  choose e he hball using hrad
  -- a Lebesgue number of the cover of `[m₁, m₂] ⊆ ℂ`
  have hcpt : IsCompact (((↑) : ℝ → ℂ) '' Icc m₁ m₂) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hcover : ((↑) : ℝ → ℂ) '' Icc m₁ m₂ ⊆ ⋃ y : Icc m₁ m₂, ball ((y : ℝ) : ℂ) (e y) := by
    rintro _ ⟨y, hy, rfl⟩
    exact mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (he _)⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hcpt (fun _ => isOpen_ball) hcover
  refine ⟨min ε δ, lt_min hε hδ, fun z hz hzn => ?_⟩
  by_cases hzK : z ∈ fwdHull W t₁
  · exact (fwdHull_mono.1 (show t₁ ≤ t₁ + s by linarith)) hzK
  by_contra hzK'
  have hzO : z ∈ H \ fwdHull W (t₁ + s) := ⟨hz, hzK'⟩
  obtain ⟨hwO, -⟩ := fwdMap_add_shift hW hW0 ht₁ hs hzO
  set w := fwdMap W t₁ z with hw
  have hzO₁ : z ∈ H \ fwdHull W t₁ := ⟨hz, hzK⟩
  have hre := hcl z hzO₁ (hzn.trans_le (min_le_left _ _))
  have him : w.im ≤ z.im := im_fwdMap_le hW hW0 ht₁ hzO₁
  have hwim : 0 < w.im := hwO.1
  obtain ⟨y, hy⟩ := hleb ((w.re : ℝ) : ℂ) ⟨w.re, hre, rfl⟩
  have hwball : w ∈ ball ((w.re : ℝ) : ℂ) δ := by
    rw [mem_ball, dist_eq_norm]
    have e1 : w - ((w.re : ℝ) : ℂ) = (w.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [e1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hwim]
    have hzim : z.im ≤ ‖z‖ := Complex.im_le_norm z
    linarith [min_le_right ε δ]
  have hwy := hy hwball
  rw [mem_ball, dist_eq_norm] at hwy
  exact hwO.2 (hball y w hwO.1 hwy)

/-! ### The fiber lies inside the force interval -/

/-- **The cluster condition from swallowed points on both sides.** Let `η` be a continuous Loewner trace of `W`
before `T > σ`. If real points `y₁ < 0 < y₂` are swallowed by `σ`, and every real `c > r` (resp. `c < ℓ`) is the
image `Y(σ)` of a real solution `Y` of the centred flow from a point `Y(0) > 0` (resp. `< 0`), then for some
`ε > 0` and `ℓ < m₁`, `m₂ < r`, every `z ∈ ℍ \ K_σ` with `‖z‖ < ε` has `Re f_σ(z) ∈ [m₁, m₂]`. -/
theorem exists_cluster_bounds {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T σ : ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTraceLT W T η) (hσ : 0 ≤ σ) (hσT : σ < T) {ℓ r y₁ y₂ : ℝ} (hy₁ : y₁ < 0)
    (hy₂ : 0 < y₂) (hd₁ : ¬ ∃ v, IsForwardSol W (y₁ : ℂ) σ v) (hd₂ : ¬ ∃ v, IsForwardSol W (y₂ : ℂ) σ v)
    (hR : ∀ c : ℝ, r < c → ∃ Y : ℝ → ℝ, IsForwardSol W (Y 0 : ℂ) σ (fun s => (Y s : ℂ)) ∧ Y σ = c ∧ 0 < Y 0)
    (hL : ∀ c : ℝ, c < ℓ → ∃ Y : ℝ → ℝ, IsForwardSol W (Y 0 : ℂ) σ (fun s => (Y s : ℂ)) ∧ Y σ = c ∧ Y 0 < 0) :
    ∃ ε > (0 : ℝ), ∃ m₁ m₂ : ℝ, ℓ < m₁ ∧ m₂ < r ∧
      ∀ z ∈ H \ fwdHull W σ, ‖z‖ < ε → m₁ ≤ (fwdMap W σ z).re ∧ (fwdMap W σ z).re ≤ m₂ := by
  set F := extendFrom H (fwdMapInv W σ) with hFdef
  have hFc : ContinuousOn F Hbar := (hη.hasBdryLimits hW hW0 hσ hσT).continuousOn
  have hFH : ∀ w ∈ H, F w = fwdMapInv W σ w := fun w hw =>
    extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 hσ) hw
  -- real points beyond the forces map to physical points beyond the swallowed ones
  have hRv : ∀ c : ℝ, r < c → ∃ x : ℝ, y₂ < x ∧ F (c : ℂ) = x := by
    intro c hc
    obtain ⟨Y, hY, hYσ, hY0⟩ := hR c hc
    have hF := hη.extendFrom_eq_of_isForwardSol hW hW0 hσ hσT hY
    rw [hYσ] at hF
    refine ⟨Y 0, ?_, hF⟩
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · exact hd₂ (exists_isForwardSol_of_lt hW hσ (by rw [hW0]; exact hY0) hlt hY)
    · exact hd₂ ⟨_, heq ▸ hY⟩
  have hLv : ∀ c : ℝ, c < ℓ → ∃ x : ℝ, x < y₁ ∧ F (c : ℂ) = x := by
    intro c hc
    obtain ⟨Y, hY, hYσ, hY0⟩ := hL c hc
    have hF := hη.extendFrom_eq_of_isForwardSol hW hW0 hσ hσT hY
    rw [hYσ] at hF
    refine ⟨Y 0, ?_, hF⟩
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with hlt | heq
    · exact hd₁ (Aux25.exists_isForwardSol_of_lt_left hW hσ (by rw [hW0]; exact hY0) hlt hY)
    · exact hd₁ ⟨_, heq.symm ▸ hY⟩
  -- closing: at the force coordinates themselves
  have hRe : ∀ c : ℝ, r ≤ c → y₂ ≤ (F (c : ℂ)).re := by
    intro c hc
    have hlim : Tendsto (fun n : ℕ => ((c + 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[Hbar] (c : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => mem_Hbar_of_im_eq_zero (by simp)⟩
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add c
      rw [add_zero] at h
      exact (Complex.continuous_ofReal.tendsto c).comp h
    have hcont := ((Complex.continuous_re.tendsto _).comp ((hFc (c : ℂ) (mem_Hbar_of_im_eq_zero
      (by simp))).tendsto.comp hlim))
    refine ge_of_tendsto hcont (Eventually.of_forall fun n => ?_)
    obtain ⟨x, hx, hFx⟩ := hRv (c + 1 / ((n : ℝ) + 1)) (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      linarith)
    simp only [Function.comp_apply, hFx, Complex.ofReal_re]
    exact hx.le
  have hLe : ∀ c : ℝ, c ≤ ℓ → (F (c : ℂ)).re ≤ y₁ := by
    intro c hc
    have hlim : Tendsto (fun n : ℕ => ((c - 1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[Hbar] (c : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => mem_Hbar_of_im_eq_zero (by simp)⟩
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub c
      rw [sub_zero] at h
      exact (Complex.continuous_ofReal.tendsto c).comp h
    have hcont := ((Complex.continuous_re.tendsto _).comp ((hFc (c : ℂ) (mem_Hbar_of_im_eq_zero
      (by simp))).tendsto.comp hlim))
    refine le_of_tendsto hcont (Eventually.of_forall fun n => ?_)
    obtain ⟨x, hx, hFx⟩ := hLv (c - 1 / ((n : ℝ) + 1)) (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
      linarith)
    simp only [Function.comp_apply, hFx, Complex.ofReal_re]
    exact hx.le
  -- the cluster condition, by compactness
  by_contra hcon
  have hseq : ∀ n : ℕ, ∃ z ∈ H \ fwdHull W σ, ‖z‖ < 1 / ((n : ℝ) + 1) ∧
      ((fwdMap W σ z).re < ℓ + 1 / ((n : ℝ) + 1) ∨ r - 1 / ((n : ℝ) + 1) < (fwdMap W σ z).re) := by
    intro n
    by_contra h
    push Not at h
    exact hcon ⟨1 / ((n : ℝ) + 1), Nat.one_div_pos_of_nat, ℓ + 1 / ((n : ℝ) + 1), r - 1 / ((n : ℝ) + 1),
      by linarith [(Nat.one_div_pos_of_nat : (0 : ℝ) < 1 / ((n : ℝ) + 1))],
      by linarith [(Nat.one_div_pos_of_nat : (0 : ℝ) < 1 / ((n : ℝ) + 1))],
      fun z hz hzn => h z hz hzn⟩
  choose z hzO hzn hzout using hseq
  have hz0 : Tendsto z atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hzn n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  set w : ℕ → ℂ := fun n => fwdMap W σ (z n) with hwdef
  have hwH : ∀ n, w n ∈ H := fun n => FwdHolo.mapsTo_fwdMap hW hσ (hzO n)
  have hFw : ∀ n, fwdMapInv W σ (w n) = z n := fun n => fwdMapInv_fwdMap hW hW0 hσ (hzO n)
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hσ
  have hwb : ∀ n, w n ∈ closedBall (0 : ℂ) (1 + max C 0) ∩ Hbar := by
    intro n
    refine ⟨?_, H_subset_Hbar (hwH n)⟩
    rw [mem_closedBall, dist_zero_right]
    have h1 := hC (w n) (hwH n)
    rw [hFw n] at h1
    have h2 := norm_sub_norm_le (w n) (z n)
    rw [norm_sub_rev] at h1
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    linarith [hzn n, le_max_left C 0]
  obtain ⟨w', hw'mem, φ, hφ, hlimw⟩ :=
    ((isCompact_closedBall (0 : ℂ) (1 + max C 0)).inter_right isClosed_Hbar).tendsto_subseq hwb
  have hFw' : F w' = 0 := by
    have h1 : Tendsto (fun n => F (w (φ n))) atTop (𝓝 (F w')) :=
      (hFc w' hw'mem.2).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hlimw, Eventually.of_forall fun n => H_subset_Hbar (hwH (φ n))⟩)
    have h2 : ∀ n, F (w (φ n)) = z (φ n) := fun n => by rw [hFH _ (hwH _), hFw]
    exact tendsto_nhds_unique (h1.congr h2) (hz0.comp hφ.tendsto_atTop)
  have hw'R : w'.im = 0 := by
    by_contra hne
    have hw'H : w' ∈ H := lt_of_le_of_ne hw'mem.2 (Ne.symm hne)
    have h := fwdMapInv_mem_H hW hW0 hσ hw'H
    rw [← hFH w' hw'H, hFw'] at h
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h)
  have hw'eq : w' = ((w'.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw'R])
  set c := w'.re with hc
  have hrec := (Complex.continuous_re.tendsto w').comp hlimw
  -- `c` lies outside `(ℓ, r)`
  have hcout : c ≤ ℓ ∨ r ≤ c := by
    by_contra hin
    push Not at hin
    obtain ⟨h1, h2⟩ := hin
    have hgap : 0 < min (c - ℓ) (r - c) := lt_min (by linarith) (by linarith)
    have hev1 : ∀ᶠ n in atTop, |(w (φ n)).re - c| < min (c - ℓ) (r - c) / 2 := by
      have := Metric.tendsto_nhds.1 hrec _ (half_pos hgap)
      filter_upwards [this] with n hn
      rwa [Real.dist_eq] at hn
    have hev2 : ∀ᶠ n in atTop, 1 / ((φ n : ℝ) + 1) < min (c - ℓ) (r - c) / 2 := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop).eventually
        (gt_mem_nhds (half_pos hgap))
      exact this
    obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
    have hmin1 := min_le_left (c - ℓ) (r - c)
    have hmin2 := min_le_right (c - ℓ) (r - c)
    rcases hzout (φ n) with h | h
    · have := (abs_lt.1 hn1).1
      simp only [hwdef] at this
      linarith
    · have := (abs_lt.1 hn1).2
      simp only [hwdef] at this
      linarith
  rcases hcout with h | h
  · have := hLe c h
    rw [← hw'eq, hFw'] at this
    simp at this
    linarith
  · have := hRe c h
    rw [← hw'eq, hFw'] at this
    simp at this
    linarith


/-! ### The force coordinates of a frozen path, read on `[0, σ]` -/

/-- The centred force coordinate `u = v − W` of a frozen force path on `[0, T]` (driver read through a continuous
`W` agreeing with `w` there) solves the centred real Loewner equation, with integrable reciprocal and null zero
set (the preparation of `ne_of_mem_H_of_mark`). -/
theorem forceData {w : ℝ≥0 → ℝ} {W : ℝ → ℝ} {v : ℝ≥0 → ℝ} {x T : ℝ} (hT0 : 0 ≤ T)
    (hWeq : ∀ s ∈ Icc (0 : ℝ) T, W s = w s.toNNReal) (hv : Continuous v) (hWc : Continuous W)
    (hint : ∀ s : ℝ≥0, IntervalIntegrable (fun r : ℝ => (w r.toNNReal - v r.toNNReal)⁻¹) volume 0 s)
    (heq : ∀ s : ℝ≥0, v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal))
    (hnull : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ⊤ ∧ w s.toNNReal = v s.toNNReal} = 0) :
    ContinuousOn (fun s => v s.toNNReal - W s) (Icc 0 T) ∧
      (∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T, s₁ ≤ s₂ →
        (v s₂.toNNReal - W s₂) - (v s₁.toNNReal - W s₁) =
          -(W s₂ - W s₁) + ∫ s in s₁..s₂, 2 / (v s.toNNReal - W s)) ∧
      IntervalIntegrable (fun s => 2 / (v s.toNNReal - W s)) volume 0 T ∧
      volume {s | s ∈ Icc (0 : ℝ) T ∧ v s.toNNReal - W s = 0} = 0 := by
  set u : ℝ → ℝ := fun s => v s.toNNReal - W s with hu
  have hu_eq : ∀ s ∈ Icc (0 : ℝ) T, u s = v s.toNNReal - w s.toNNReal := fun s hs => by
    simp only [hu, hWeq s hs]
  have huc : ContinuousOn u (Icc 0 T) :=
    ((hv.comp continuous_real_toNNReal).sub hWc).continuousOn
  have hint' : ∀ s ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 s := by
    intro s hs
    have h := hint s.toNNReal
    rw [Real.coe_toNNReal _ hs.1] at h
    have e : (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) =
        fun r => (-2) * (w r.toNNReal - v r.toNNReal)⁻¹ := by
      funext r
      rw [div_eq_mul_inv, ← neg_sub, inv_neg]
      ring
    rw [e]
    exact h.const_mul _
  have heq' : ∀ s ∈ Icc (0 : ℝ) T,
      v s.toNNReal = x + ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal) := by
    intro s hs
    have h := heq s.toNNReal
    rwa [Real.coe_toNNReal _ hs.1] at h
  have hcongr : ∀ s₁ ∈ Icc (0 : ℝ) T, ∀ s₂ ∈ Icc (0 : ℝ) T,
      (∫ r in s₁..s₂, 2 / (v r.toNNReal - w r.toNNReal)) = ∫ r in s₁..s₂, 2 / u r := by
    intro s₁ hs₁ s₂ hs₂
    refine intervalIntegral.integral_congr fun r hr => ?_
    simp only [hu_eq r (uIcc_subset_Icc hs₁ hs₂ hr)]
  refine ⟨huc, fun s₁ hs₁ s₂ hs₂ _ => ?_, ?_, ?_⟩
  · show u s₂ - u s₁ = _
    rw [← hcongr s₁ hs₁ s₂ hs₂,
      ← intervalIntegral.integral_interval_sub_left (hint' s₂ hs₂) (hint' s₁ hs₁)]
    have e1 := heq' s₁ hs₁
    have e2 := heq' s₂ hs₂
    simp only [hu]
    linarith
  · have h := hint' T ⟨hT0, le_rfl⟩
    rw [intervalIntegrable_iff] at h ⊢
    refine h.congr_fun (fun r hr => ?_) measurableSet_uIoc
    rw [uIoc_of_le hT0] at hr
    show 2 / (v r.toNNReal - w r.toNNReal) = 2 / u r
    simp only [hu_eq r ⟨hr.1.le, hr.2⟩]
  · refine measure_mono_null (fun s hs => ?_) hnull
    refine ⟨hs.1.1, ENNReal.coe_lt_top, ?_⟩
    have h := hs.2
    change u s = 0 at h
    rw [hu_eq s hs.1] at h
    linarith

/-- **The cluster condition for a frozen one-mark-per-side path with marks at the seed** (the two-seed word),
with infinite lifetime and a generating trace: if real points `y₁ < 0 < y₂` are swallowed by `σ`, the cluster
condition holds at `σ` with an interval strictly inside the force interval `(V^L_σ − W_σ, V^R_σ − W_σ)`. -/
theorem exists_cluster_of_path {a : ℝ} {xL xR ρL ρR : Fin 1 → ℝ} (hxL : xL 0 = 0) (hxR : xR 0 = 0)
    {w : ℝ≥0 → ℝ} {vL vR : Fin 1 → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ⊤) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η)
    (σ : ℝ≥0) {y₁ y₂ : ℝ} (hy₁ : y₁ < 0) (hy₂ : 0 < y₂)
    (hd₁ : ¬ ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (y₁ : ℂ) σ v)
    (hd₂ : ¬ ∃ v, IsForwardSol (fun s : ℝ => w s.toNNReal) (y₂ : ℂ) σ v) :
    ∃ ε > (0 : ℝ), ∃ m₁ m₂ : ℝ, vL 0 σ - w σ < m₁ ∧ m₂ < vR 0 σ - w σ ∧
      ∀ z ∈ H \ fwdHull (fun s : ℝ => w s.toNNReal) σ, ‖z‖ < ε →
        m₁ ≤ (fwdMap (fun s : ℝ => w s.toNNReal) σ z).re ∧
          (fwdMap (fun s : ℝ => w s.toNNReal) σ z).re ≤ m₂ := by
  obtain ⟨hwc, hw0⟩ := Sec7.IsIntegratedSLEPath.continuous_w_of_top hp
  obtain ⟨-, hvL0, hvR0, -, hvLc, hvRc, -, hvLw, hwvR, -, hgapL, hgapR, -, hvLeq, hvReq, hcolL,
    hcolR, -⟩ := hp
  have hvLc' : Continuous (vL 0) := continuousOn_univ.1 (by simpa using hvLc 0)
  have hvRc' : Continuous (vR 0) := continuousOn_univ.1 (by simpa using hvRc 0)
  set t₂ : ℝ := (σ : ℝ) + 1 with ht₂
  have hσt₂ : (σ : ℝ) < t₂ := by linarith
  have ht₂T : ENNReal.ofReal t₂ < (⊤ : ℝ≥0∞) := ENNReal.ofReal_lt_top
  set W := frozenDrive w t₂ with hWdef
  have hWc : Continuous W := continuous_frozenDrive_of_lt hwc.continuousOn ht₂T
  have hW0 : W 0 = 0 := by rw [hWdef, frozenDrive_zero (by positivity), hw0]
  have hL := hη.isLoewnerTraceLT ht₂T
  have hσ0 : (0 : ℝ) ≤ σ := σ.coe_nonneg
  have hWeq : ∀ s ∈ Icc (0 : ℝ) t₂, W s = w s.toNNReal := fun s hs => frozenDrive_eq hs
  have hWeqσ : ∀ s ∈ Icc (0 : ℝ) σ, W s = w s.toNNReal := fun s hs => hWeq s ⟨hs.1, hs.2.trans hσt₂.le⟩
  have hagree : ∀ r ∈ Icc (0 : ℝ) σ, (fun s : ℝ => w s.toNNReal) r = W r := fun r hr => (hWeqσ r hr).symm
  -- the swallowed points for `W`
  have hd₁' : ¬ ∃ v, IsForwardSol W (y₁ : ℂ) σ v := fun ⟨v, hv⟩ =>
    hd₁ ⟨v, QuantumZipper.isForwardSol_congr_drive hWeqσ hv⟩
  have hd₂' : ¬ ∃ v, IsForwardSol W (y₂ : ℂ) σ v := fun ⟨v, hv⟩ =>
    hd₂ ⟨v, QuantumZipper.isForwardSol_congr_drive hWeqσ hv⟩
  -- the two force coordinates
  obtain ⟨huRc, huReq, huRint, huRnull⟩ := forceData hσ0 hWeqσ hvRc' hWc (fun s => hgapR s (by simp) 0)
    (fun s => hvReq s (by simp) 0) (hcolR 0)
  obtain ⟨huLc, huLeq, huLint, huLnull⟩ := forceData hσ0 hWeqσ hvLc' hWc (fun s => hgapL s (by simp) 0)
    (fun s => hvLeq s (by simp) 0) (hcolL 0)
  have huR0 : ∀ s ∈ Icc (0 : ℝ) σ, 0 ≤ vR 0 s.toNNReal - W s := fun s hs => by
    rw [hWeqσ s hs]; linarith [hwvR s.toNNReal (by simp) 0]
  have huL0 : ∀ s ∈ Icc (0 : ℝ) σ, vL 0 s.toNNReal - W s ≤ 0 := fun s hs => by
    rw [hWeqσ s hs]; linarith [hvLw s.toNNReal (by simp) 0]
  have hWσ : W σ = w σ := by rw [hWeqσ σ ⟨hσ0, le_rfl⟩, Real.toNNReal_coe]
  have hσσ : (σ : ℝ).toNNReal = σ := Real.toNNReal_coe
  have hzero : (0 : ℝ).toNNReal = 0 := Real.toNNReal_zero
  obtain ⟨ε, hε, m₁, m₂, hm₁, hm₂, hcl⟩ := exists_cluster_bounds hWc hW0 hL hσ0 hσt₂
    (ℓ := vL 0 σ - w σ) (r := vR 0 σ - w σ) hy₁ hy₂ hd₁' hd₂'
    (fun c hc => by
      obtain ⟨Y, hY, hYσ, hge⟩ := Aux25.exists_isForwardSol_of_gt hWc hW0 hσ0 huRc huR0 huReq huRint
        huRnull (y := c) (by rw [hσσ, hWσ]; exact hc)
      refine ⟨Y, hY, hYσ, ?_⟩
      have h0 := hge 0 ⟨le_rfl, hσ0⟩
      rw [hzero, hvR0, hxR, hW0, hσσ, hWσ] at h0
      linarith)
    (fun c hc => by
      obtain ⟨Y, hY, hYσ, hle⟩ := Aux25.exists_isForwardSol_of_lt' hWc hW0 hσ0 huLc huL0 huLeq huLint
        huLnull (y := c) (by rw [hσσ, hWσ]; exact hc)
      refine ⟨Y, hY, hYσ, ?_⟩
      have h0 := hle 0 ⟨le_rfl, hσ0⟩
      rw [hzero, hvL0, hxL, hW0, hσσ, hWσ] at h0
      linarith)
  have hK : fwdHull (fun s : ℝ => w s.toNNReal) σ = fwdHull W σ :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hwc.comp continuous_real_toNNReal) hWc hσ0 hagree
  refine ⟨ε, hε, m₁, m₂, hm₁, hm₂, fun z hz hzn => ?_⟩
  rw [hK] at hz
  rw [fwdMap_eq_of_eqOn hσ0 hagree]
  exact hcl z hz hzn

end InteractingSLE.LP.LP4HB
