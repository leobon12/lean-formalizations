/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux61Tools
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior

/-!
# Aux. lemmas 61–62, deterministic core: the source drift is the mark drift

Packet PROVE-GB7A2. Source: specification Aux. lemma 61 (PC1) and the proof of Aux. lemma 62
(`source/spec/p241-288.md`, pp. 261–263): with `f = v'` (the difference of the reference and actual canonical means)
on a buffer of the path and the Cameron–Martin source `v = −(2π)⁻¹ Δ f` outside it, the Cameron–Martin drift is
the drift difference of the two words. In this project's field-free form (the Girsanov drift of the comparison is
computed from the path alone):

* `compFun`: `R_s = G_{ℍ∖K_s} v − argSum_s + argSum_0 − f` on `ℍ ∖ K_s`;
* `compFun_eq_integral`: `R_s(y) = ∫₀ˢ Im(2/f_u(y)) (markDrift(u) − A(u)) du` (Hadamard and the arg-sum dynamics);
* `compFun_eq_zero`: **`R_s = 0`** — `R_s ∘ F_s` is a bounded harmonic function on `ℍ` (the imaginary part of a
  holomorphic function) with boundary value `0` at every real point: near an alive real point by the integral form,
  elsewhere (the image of the hull and of the seed) by the defining form, where `f = argSum_0`, the Green potential
  vanishes and the arg sum has the seed value `0`;
* `srcDrift_eq_markDrift`: **the source drift equals the mark drift** `A(u) = ∑ⱼ cⱼ / Re f_u(p_j)` on `[0, t]`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Interval

namespace InteractingSLE

namespace GB7a

open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol greenH fwdMapInv)

variable {W : ℝ → ℝ} {ι : Type*} [Fintype ι]

/-- The comparison function `R_s = G_{ℍ∖K_s} v − argSum_s + argSum_0 − f`. -/
def compFun (W : ℝ → ℝ) (v : ℂ → ℝ) (p c : ι → ℝ) (c₀ : ℝ) (f : ℂ → ℝ) (s : ℝ) (y : ℂ) : ℝ :=
  greenPot W v s y - argSum W p c c₀ s y + argSum W p c c₀ 0 y - f y

/-- The drift gap `markDrift − A`. -/
def driftGap (W : ℝ → ℝ) (v : ℂ → ℝ) (p c : ι → ℝ) (u : ℝ) : ℝ := markDrift W p c u - srcDrift W v u

section Basic

variable {v : ℂ → ℝ} {t Cv R m : ℝ} {p c : ι → ℝ} {c₀ : ℝ} {f : ℂ → ℝ}

theorem continuousOn_driftGap (hW : Continuous W) (ht : 0 ≤ t) (hv : IsSrc W v t Cv R m)
    (hp : MarksAlive W p t) : ContinuousOn (driftGap W v p c) (Icc 0 t) :=
  (continuousOn_markDrift hW hp).sub (hv.continuousOn_srcDrift hW ht)

/-- **The integral form** `R_s(y) = ∫₀ˢ Im(2/f_u(y)) (markDrift(u) − A(u)) du`. -/
theorem compFun_eq_integral (hW : Continuous W) (hv : IsSrc W v t Cv R m) (hp : MarksAlive W p t)
    (hGf : ∀ y ∈ H, greenPot0 v y = f y) {s : ℝ} (hs : s ∈ Icc 0 t) {y : ℂ} (hy : y ∈ H \ fwdHull W s) :
    compFun W v p c c₀ f s y = ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * driftGap W v p c u := by
  have ht : 0 ≤ t := hs.1.trans hs.2
  have h1 := hv.greenPot_eq hW hs hy
  have h2 := argSum_eq_sub_integral (c := c) hW hs.1 c₀ (hp.mono hs) hy ⟨hs.1, le_rfl⟩
  have hk : ContinuousOn (fun u => (2 / fwdMap W u y).im) (Icc 0 s) :=
    Complex.continuous_im.comp_continuousOn (continuousOn_const.div (Ito.continuousOn_fwdMap_time' hW hs.1 hy)
      fun u hu => Ito.fwdMap_ne_zero hW hs.1 hy hu)
  have hsub : Icc 0 s ⊆ Icc 0 t := Icc_subset_Icc le_rfl hs.2
  have i1 : IntervalIntegrable (fun u => (2 / fwdMap W u y).im * srcDrift W v u) volume 0 s :=
    (hk.mul ((hv.continuousOn_srcDrift hW ht).mono hsub)).intervalIntegrable_of_Icc hs.1
  have i2 : IntervalIntegrable (fun u => (2 / fwdMap W u y).im * markDrift W p c u) volume 0 s :=
    (hk.mul ((continuousOn_markDrift hW hp).mono hsub)).intervalIntegrable_of_Icc hs.1
  have hsplit : ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * driftGap W v p c u =
      (∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * markDrift W p c u) -
        ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * srcDrift W v u := by
    rw [← intervalIntegral.integral_sub i2 i1]
    congr 1; funext u; simp only [driftGap]; ring
  rw [hsplit, compFun, h1, h2, hGf y hy.1]
  ring

/-- `|argSum| ≤ |c₀| + π ∑ |cⱼ|`. -/
theorem abs_argSum_le (W : ℝ → ℝ) (p c : ι → ℝ) (c₀ : ℝ) (s : ℝ) (y : ℂ) :
    |argSum W p c c₀ s y| ≤ |c₀| + Real.pi * ∑ j, |c j| := by
  rw [argSum, Finset.mul_sum]
  refine (abs_add_le _ _).trans (add_le_add_right ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => ?_)) _)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (Complex.abs_arg_le_pi _) (abs_nonneg _)

/-- **The comparison function is bounded** on `ℍ ∖ K_s`. -/
theorem abs_compFun_le (hW : Continuous W) (hv : IsSrc W v t Cv R m) (hGf : ∀ y ∈ H, greenPot0 v y = f y)
    {s : ℝ} (hs : s ∈ Icc 0 t) {y : ℂ} (hy : y ∈ H \ fwdHull W s) :
    |compFun W v p c c₀ f s y| ≤ 2 * IsSrc.greenBound Cv R + 2 * (|c₀| + Real.pi * ∑ j, |c j|) := by
  have h1 := hv.abs_greenPot_le hW hs hy
  have h2 := abs_argSum_le W p c c₀ s y
  have h3 := abs_argSum_le W p c c₀ 0 y
  have h4 : |f y| ≤ IsSrc.greenBound Cv R := by rw [← hGf y hy.1]; exact hv.abs_greenPot0_le hy.1
  rw [compFun]
  calc |greenPot W v s y - argSum W p c c₀ s y + argSum W p c c₀ 0 y - f y|
      ≤ |greenPot W v s y| + |argSum W p c c₀ s y| + |argSum W p c c₀ 0 y| + |f y| := by
        have e1 := abs_sub (greenPot W v s y - argSum W p c c₀ s y + argSum W p c c₀ 0 y) (f y)
        have e2 := abs_add_le (greenPot W v s y - argSum W p c c₀ s y) (argSum W p c c₀ 0 y)
        have e3 := abs_sub (greenPot W v s y) (argSum W p c c₀ s y)
        linarith
    _ ≤ _ := by linarith

/-- An alive point is not `0` (`W 0 = 0`). -/
theorem ne_zero_of_isForwardSol (hW0 : W 0 = 0) {z : ℂ} {T : ℝ} (hT : 0 ≤ T) {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) : z ≠ 0 := by
  have h := hu.2 0 ⟨le_rfl, hT⟩
  rw [h.2] at h
  simpa [hW0] using h.1

/-- **Near an alive real point the kernel is small**: if `u` is the real flow from `a`, `2δ ≤ |u|` on `[0, s]`
and `‖y − a‖ e^{2s/δ²} < δ`, then `|Im(2/f_r(y))| ≤ 2 ‖y − a‖ e^{2s/δ²} / δ²` on `[0, s]`. -/
theorem abs_im_two_div_le_near_real (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) {a : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (a : ℂ) s u) {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ r ∈ Icc (0 : ℝ) s, 2 * δ ≤ ‖u r‖)
    {y : ℂ} (hy : y ∈ H \ fwdHull W s) (hya : ‖y - a‖ * Real.exp (2 / δ ^ 2 * s) < δ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) s) :
    |(2 / fwdMap W r y).im| ≤ 2 * (‖y - a‖ * Real.exp (2 / δ ^ 2 * s)) / δ ^ 2 := by
  obtain ⟨v, hv⟩ := Ito.exists_isForwardSol_of_mem hs hy
  have hst := norm_sub_le_of_isForwardSol hW hu hv hδ hs le_rfl hlow hya r hr
  have hexp : ‖y - a‖ * Real.exp (2 / δ ^ 2 * r) ≤ ‖y - a‖ * Real.exp (2 / δ ^ 2 * s) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hr.2 (by positivity)))
      (norm_nonneg _)
  set D := ‖y - a‖ * Real.exp (2 / δ ^ 2 * s) with hD
  have hvu : ‖v r - u r‖ ≤ D := hst.trans hexp
  have hfr : fwdMap W r y = v r := fwdMap_eq_of_isForwardSol hW hv hr
  have hur : (u r).im = 0 := im_eq_zero_of_isForwardSol_real hW hu hr
  have hnorm : δ ≤ ‖v r‖ := by
    have := norm_sub_norm_le (u r) (v r)
    rw [norm_sub_rev] at this
    linarith [hlow r hr]
  have him : |(v r).im| ≤ D := by
    have : (v r).im = (v r - u r).im := by simp [hur]
    rw [this]; exact (Complex.abs_im_le_norm _).trans hvu
  rw [hfr]
  have hv0 : v r ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; linarith
  have hns : 0 < Complex.normSq (v r) := Complex.normSq_pos.2 hv0
  have hsq : δ ^ 2 ≤ Complex.normSq (v r) := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ hδ.le hnorm 2
  rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_im, Complex.inv_re]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
  rw [show 2 * (-(v r).im / Complex.normSq (v r)) = -(2 * (v r).im) / Complex.normSq (v r) by ring,
    abs_div, abs_neg, abs_of_pos hns, abs_mul, abs_two]
  rw [div_le_div_iff₀ hns (by positivity)]
  have hD0 : 0 ≤ D := by positivity
  calc 2 * |(v r).im| * δ ^ 2 ≤ 2 * D * δ ^ 2 := by gcongr
    _ ≤ 2 * D * Complex.normSq (v r) := by gcongr

/-- **`R_s → 0` at an alive real point** (the integral form). -/
theorem tendsto_compFun_of_alive (hW : Continuous W) (hv : IsSrc W v t Cv R m) (hp : MarksAlive W p t)
    (hGf : ∀ y ∈ H, greenPot0 v y = f y) {s : ℝ} (hs : s ∈ Icc 0 t) {a : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (a : ℂ) s u) :
    Tendsto (compFun W v p c c₀ f s) (𝓝[H \ fwdHull W s] (a : ℂ)) (𝓝 0) := by
  have ht : 0 ≤ t := hs.1.trans hs.2
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hs.1 hu
  set E := Real.exp (2 / δ ^ 2 * s) with hE
  have hE0 : 0 < E := Real.exp_pos _
  obtain ⟨Ce, hCe⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((continuousOn_driftGap (c := c) hW ht hv hp).mono (Icc_subset_Icc le_rfl hs.2))
  have hCe0 : 0 ≤ Ce := (norm_nonneg _).trans (hCe 0 ⟨le_rfl, hs.1⟩)
  set g : ℂ → ℝ := fun y => s * (2 * (‖y - a‖ * E) / δ ^ 2 * Ce) with hg
  have hg0 : Tendsto g (𝓝[H \ fwdHull W s] (a : ℂ)) (𝓝 0) := by
    have hc : Continuous g := by
      simp only [hg]; fun_prop
    have := hc.tendsto (a : ℂ)
    simp only [hg, sub_self, norm_zero, zero_mul, mul_zero, zero_div] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ y : ℂ in 𝓝[H \ fwdHull W s] (a : ℂ), ‖y - (a : ℂ)‖ * E < δ := by
    have hc : Continuous fun y : ℂ => ‖y - (a : ℂ)‖ * E :=
      (continuous_norm.comp (continuous_id.sub continuous_const)).mul continuous_const
    have h0 : ‖(a : ℂ) - (a : ℂ)‖ * E < δ := by simpa using hδ
    exact nhdsWithin_le_nhds (hc.continuousAt.eventually (gt_mem_nhds h0))
  refine squeeze_zero_norm' ?_ hg0
  filter_upwards [hnear, self_mem_nhdsWithin] with y hya hy
  rw [compFun_eq_integral hW hv hp hGf hs hy, Real.norm_eq_abs]
  have hb : ∀ r ∈ Ι (0 : ℝ) s, ‖(2 / fwdMap W r y).im * driftGap W v p c r‖ ≤
      2 * (‖y - a‖ * E) / δ ^ 2 * Ce := by
    intro r hr
    rw [uIoc_of_le hs.1] at hr
    have hrI : r ∈ Icc (0 : ℝ) s := ⟨hr.1.le, hr.2⟩
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul (abs_im_two_div_le_near_real hW hs.1 hu hδ hlow hy hya hrI) (hCe r hrI) (norm_nonneg _)
      (by positivity)
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg hs.1, Real.norm_eq_abs] at this
  simp only [hg]
  linarith

end Basic

/-! ### The comparison function vanishes -/

section Main

variable {v : ℂ → ℝ} {t Cv R m : ℝ} {p c : ι → ℝ} {c₀ : ℝ} {f : ℂ → ℝ} {N : Set ℂ} {η : ℝ → ℂ}

/-- The hypotheses of the drift identity on `[0, t]`. -/
structure IdentHyp (W : ℝ → ℝ) (t : ℝ) (η : ℝ → ℂ) (p c : ι → ℝ) (c₀ : ℝ) (v : ℂ → ℝ) (Cv R m : ℝ)
    (f : ℂ → ℝ) (N : Set ℂ) : Prop where
  cont : Continuous W
  zero : W 0 = 0
  t_pos : 0 < t
  trace_cont : ContinuousOn η (Icc 0 t)
  fill : ∀ s ∈ Ioc (0 : ℝ) t, fwdHull W s = fillH (η '' Icc 0 s)
  marks : MarksAlive W p t
  seed : c₀ + Real.pi * ∑ j ∈ Finset.univ.filter (fun j => 0 < p j), c j = 0
  src : IsSrc W v t Cv R m
  open_N : IsOpen N
  hull_N : closure (fwdHull W t) ⊆ N
  zero_N : (0 : ℂ) ∈ N
  src_N : ∀ z, v z ≠ 0 → z ∉ N
  green : ∀ y ∈ H, greenPot0 v y = f y
  f_eq : ∀ y ∈ N ∩ H, f y = argSum W p c c₀ 0 y

/-- `Im f_s(z) ≤ Im z`. -/
theorem im_fwdMap_le_im (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {z : ℂ}
    (hz : z ∈ H \ fwdHull W s) : (fwdMap W s z).im ≤ z.im := by
  have hanti := (QuantumZipper.im_isForwardSol_le hW hz.1 (Ito.isForwardSol_fwdMap_of_mem hW hs hz)).1
    ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  have h0 : fwdMap W 0 z = z := by
    rw [Ito.fwdMap_eq_sub_add_integral hW hs hz ⟨le_rfl, hs⟩]; simp [hW0]
  simp only at hanti
  rwa [h0] at hanti

/-- **The Green potential vanishes at the boundary in the chart** near the image of a point of `N`. -/
theorem tendsto_greenPot_extension (hI : IdentHyp W t η p c c₀ v Cv R m f N) {s : ℝ} (hs : s ∈ Icc 0 t)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W s) H) (hFc : ContinuousOn F Hbar) {x₀ : ℝ} (hF0 : F x₀ ∈ N) :
    Tendsto (fun ξ => greenPot W v s (F ξ)) (𝓝[H] (x₀ : ℂ)) (𝓝 0) := by
  have hW := hI.cont
  have hv := hI.src
  have hs0 := hs.1
  have hx₀ : (x₀ : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  -- a neighbourhood of `x₀` mapped into `N`
  have hev : ∀ᶠ ξ in 𝓝[Hbar] (x₀ : ℂ), F ξ ∈ N := (hFc _ hx₀).tendsto (hI.open_N.mem_nhds hF0)
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhdsWithin_iff.1 hev
  set d := ε / 2 with hd
  have hd0 : 0 < d := by positivity
  have hfar : ∀ ξ : ℂ, dist ξ (x₀ : ℂ) < d → ∀ z, v z ≠ 0 → d ≤ ‖ξ - fwdMap W s z‖ := by
    intro ξ hξ z hz
    by_contra hlt
    rw [not_le] at hlt
    have hzs : z ∈ H \ fwdHull W s := Ito.mem_diff_fwdHull_of_le (hv.alive z hz) hs.2
    have hfz : fwdMap W s z ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs0 hzs
    have hdist : dist (fwdMap W s z) x₀ < ε := by
      calc dist (fwdMap W s z) x₀ ≤ dist (fwdMap W s z) ξ + dist ξ x₀ := dist_triangle _ _ _
        _ < d + d := by rw [dist_eq_norm, norm_sub_rev]; exact add_lt_add hlt hξ
        _ = ε := by rw [hd]; ring
    have hN : F (fwdMap W s z) ∈ N :=
      hεN ⟨Metric.mem_ball.2 hdist, show (0 : ℝ) ≤ (fwdMap W s z).im from le_of_lt hfz⟩
    rw [hFeq hfz, QuantumZipper.RS.fwdMapInv_fwdMap hW hI.zero hs0 hzs] at hN
    exact hI.src_N z hz hN
  -- the bound
  set C := 2 * R * Cv * (volume (closedBall (0 : ℂ) R)).toReal / d ^ 2 with hC
  have hb : ∀ᶠ ξ in 𝓝[H] (x₀ : ℂ), ‖greenPot W v s (F ξ)‖ ≤ C * ξ.im := by
    have hnear : ∀ᶠ ξ : ℂ in 𝓝[H] (x₀ : ℂ), dist ξ (x₀ : ℂ) < d :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds _ hd0)
    filter_upwards [hnear, self_mem_nhdsWithin] with ξ hξd hξH
    have hξH' : 0 < ξ.im := hξH
    rw [greenPot, hFeq hξH, QuantumZipper.RS.fwdMap_fwdMapInv hW hI.zero hs0 hξH]
    have hball : Integrable fun z : ℂ => (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z :=
      (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
    refine (norm_integral_le_integral_norm _).trans ((integral_mono_of_nonneg (ae_of_all _ fun _ =>
      norm_nonneg _) (hball.const_mul (2 * ξ.im * R / d ^ 2 * Cv)) (ae_of_all _ fun z => ?_)).trans
      (le_of_eq ?_))
    · simp only [Real.norm_eq_abs]
      by_cases hz : v z = 0
      · rw [hz, mul_zero, abs_zero]
        by_cases hzb : z ∈ closedBall (0 : ℂ) R
        · have hR0 : 0 ≤ R := (norm_nonneg z).trans (by rwa [mem_closedBall, dist_zero_right] at hzb)
          rw [Set.indicator_of_mem hzb, mul_one]
          have := hv.Cv_nonneg
          positivity
        · rw [Set.indicator_of_notMem hzb, mul_zero]
      · have hzs : z ∈ H \ fwdHull W s := Ito.mem_diff_fwdHull_of_le (hv.alive z hz) hs.2
        have hfz : 0 < (fwdMap W s z).im := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs0 hzs
        have hzR := hv.norm_le z hz
        have hfar' := hfar ξ hξd z hz
        have hne : ξ ≠ fwdMap W s z := fun h => by rw [h, sub_self, norm_zero] at hfar'; linarith
        have hg0 : 0 ≤ greenH ξ (fwdMap W s z) := QuantumZipper.greenH_nonneg
          (show ξ ∈ Hbar from hξH'.le) (show fwdMap W s z ∈ Hbar from hfz.le) hne
        have hgle := greenH_le_of_mem_H hξH' hfz hne
        have himz : (fwdMap W s z).im ≤ R := (im_fwdMap_le_im hW hI.zero hs0 hzs).trans
          ((le_abs_self _).trans ((Complex.abs_im_le_norm z).trans hzR))
        have hsq : d ^ 2 ≤ ‖ξ - fwdMap W s z‖ ^ 2 := pow_le_pow_left₀ hd0.le hfar' 2
        have hg' : greenH ξ (fwdMap W s z) ≤ 2 * ξ.im * R / d ^ 2 := by
          refine hgle.trans ?_
          have hn0 : 0 < ‖ξ - fwdMap W s z‖ ^ 2 := by
            have : 0 < ‖ξ - fwdMap W s z‖ := hd0.trans_le hfar'
            positivity
          rw [div_le_div_iff₀ hn0 (by positivity)]
          have h1 : 2 * ξ.im * (fwdMap W s z).im ≤ 2 * ξ.im * R :=
            mul_le_mul_of_nonneg_left himz (by positivity)
          have h2 : 0 ≤ 2 * ξ.im * (fwdMap W s z).im := by positivity
          nlinarith
        rw [Set.indicator_of_mem (by rwa [mem_closedBall, dist_zero_right]), mul_one, abs_mul,
          abs_of_nonneg hg0]
        exact mul_le_mul hg' (hv.bound z) (abs_nonneg _) (by
          have := (norm_nonneg z).trans hzR; positivity)
    · rw [integral_const_mul, integral_indicator measurableSet_closedBall, setIntegral_const, smul_eq_mul,
        mul_one, measureReal_def, hC]
      ring
  refine squeeze_zero_norm' hb ?_
  have hc : Continuous fun ξ : ℂ => C * ξ.im := continuous_const.mul Complex.continuous_im
  have := hc.tendsto (x₀ : ℂ)
  simp only [Complex.ofReal_im, mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `arg(ξ − P) → π·[x₀ < P]` as `ξ → x₀` in `ℍ`, for real `P ≠ x₀`. -/
theorem tendsto_arg_sub_real {x₀ P : ℝ} (hne : x₀ ≠ P) :
    Tendsto (fun ξ : ℂ => Complex.arg (ξ - P)) (𝓝[H] (x₀ : ℂ))
      (𝓝 (if x₀ < P then Real.pi else 0)) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [ite_eq_left_iff.2 (fun h => absurd hlt h)]
    have hw : ((x₀ : ℂ) - P).re < 0 := by simp; linarith
    have hw' : ((x₀ : ℂ) - P).im = 0 := by simp
    have hc := Complex.continuousWithinAt_arg_of_re_neg_of_im_zero hw hw'
    have harg : Complex.arg ((x₀ : ℂ) - P) = Real.pi := by
      rw [← Complex.ofReal_sub]; exact Complex.arg_ofReal_of_neg (by linarith)
    rw [← harg]
    refine hc.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · exact ((continuous_id.sub continuous_const).tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ξ hξ
      show 0 ≤ (ξ - P).im
      have : 0 < ξ.im := hξ
      simp; linarith
  · have hn : ¬ x₀ < P := not_lt.2 hgt.le
    simp only [hn, ↓reduceIte]
    have hslit : ((x₀ : ℂ) - P) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.2 (Or.inl (by simp; linarith))
    have harg : Complex.arg ((x₀ : ℂ) - P) = 0 := by
      rw [← Complex.ofReal_sub]; exact Complex.arg_ofReal_of_nonneg (by linarith)
    rw [← harg]
    exact ((Complex.continuousAt_arg hslit).tendsto.comp
      ((continuous_id.sub continuous_const).tendsto _)).mono_left nhdsWithin_le_nhds

/-- **The arg sum tends to the seed value `0`** at a real point `x₀` that lies, relative to every mark image, on
the same side as the seed. -/
theorem tendsto_argSum_extension (hI : IdentHyp W t η p c c₀ v Cv R m f N) {s : ℝ} (hs : s ∈ Icc 0 t)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W s) H) {x₀ : ℝ}
    (hstar : ∀ j, x₀ ≠ (fwdMap W s (p j)).re ∧ (x₀ < (fwdMap W s (p j)).re ↔ 0 < p j)) :
    Tendsto (fun ξ => argSum W p c c₀ s (F ξ)) (𝓝[H] (x₀ : ℂ)) (𝓝 0) := by
  have hW := hI.cont
  have hs0 := hs.1
  have hreal : ∀ j, fwdMap W s (p j) = ((fwdMap W s (p j)).re : ℂ) := fun j => by
    obtain ⟨u, hu⟩ := hI.marks j
    exact Complex.ext (by simp) (by simp [im_fwdMap_real_eq_zero hW hu hs])
  have heq : (fun ξ => argSum W p c c₀ s (F ξ)) =ᶠ[𝓝[H] (x₀ : ℂ)]
      fun ξ => c₀ + ∑ j, c j * Complex.arg (ξ - ((fwdMap W s (p j)).re : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    rw [argSum, hFeq hξ, QuantumZipper.RS.fwdMap_fwdMapInv hW hI.zero hs0 hξ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hreal j, Complex.ofReal_re]
  have hlim : Tendsto (fun ξ : ℂ => c₀ + ∑ j, c j * Complex.arg (ξ - ((fwdMap W s (p j)).re : ℝ)))
      (𝓝[H] (x₀ : ℂ)) (𝓝 (c₀ + ∑ j, c j * (if 0 < p j then Real.pi else 0))) := by
    refine tendsto_const_nhds.add (tendsto_finsetSum _ fun j _ => (tendsto_const_nhds.mul ?_))
    have h := tendsto_arg_sub_real (hstar j).1
    by_cases hj : 0 < p j
    · have h2 := (hstar j).2.2 hj
      simp only [hj, h2, ↓reduceIte] at h ⊢; exact h
    · have h2 : ¬ x₀ < (fwdMap W s (p j)).re := fun h' => hj ((hstar j).2.1 h')
      simp only [hj, h2, ↓reduceIte] at h ⊢; exact h
  have hval : c₀ + ∑ j, c j * (if 0 < p j then Real.pi else 0) = 0 := by
    have hs' := hI.seed
    rw [Finset.sum_filter, Finset.mul_sum] at hs'
    have hsum : ∑ j, c j * (if 0 < p j then Real.pi else 0) =
        ∑ j, Real.pi * (if 0 < p j then c j else 0) :=
      Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
    rw [hsum]; exact hs'
  rw [hval] at hlim
  exact hlim.congr' heq.symm

/-- **(★)**: if the boundary extension at `x₀` is not an alive real point, `x₀` lies left of every right-mark
image and right of every left-mark image (intermediate values of the real flow). -/
theorem star_of_not_alive (hI : IdentHyp W t η p c c₀ v Cv R m f N) {s : ℝ} (hs : s ∈ Icc 0 t)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W s) H) (hFc : ContinuousOn F Hbar) {x₀ : ℝ}
    (hna : ¬ ∃ a : ℝ, F x₀ = a ∧ ∃ u, IsForwardSol W (a : ℂ) s u) (j : ι) :
    x₀ ≠ (fwdMap W s (p j)).re ∧ (x₀ < (fwdMap W s (p j)).re ↔ 0 < p j) := by
  have hW := hI.cont
  have hW0 := hI.zero
  have hs0 := hs.1
  obtain ⟨u, hu⟩ := hI.marks.mono hs j
  have hp0 : p j ≠ 0 := by
    have := ne_zero_of_isForwardSol hW0 hs0 hu; exact_mod_cast this
  have hreal : ∀ {x : ℝ} {w : ℝ → ℂ}, IsForwardSol W (x : ℂ) s w → fwdMap W s x = ((fwdMap W s x).re : ℂ) :=
    fun {x w} hw => Complex.ext (by simp) (by simp [im_fwdMap_real_eq_zero hW hw ⟨hs0, le_rfl⟩])
  have hbad : ∀ x' : ℝ, (∃ w, IsForwardSol W (x' : ℂ) s w) → (fwdMap W s x').re = x₀ → False := by
    rintro x' ⟨w, hw⟩ hx'
    have h1 := extension_fwdMap_real hW hW0 hs0 hFeq hFc hw
    rw [hreal hw, hx'] at h1
    exact hna ⟨x', h1, w, hw⟩
  refine ⟨fun h => hbad (p j) ⟨u, hu⟩ h.symm, ⟨fun hlt => ?_, fun hpos => ?_⟩⟩
  · by_contra hneg
    have hneg' : p j < 0 := lt_of_le_of_ne (not_lt.1 hneg) hp0
    obtain ⟨x', -, hx', hfx'⟩ := exists_fwdMap_real_eq_of_ge hW hW0 hs0 hneg' hu (ξ := x₀) hlt.le
    exact hbad x' hx' (by rw [hfx']; simp)
  · by_contra hle
    obtain ⟨x', -, hx', hfx'⟩ := exists_fwdMap_real_eq_of_le hW hW0 hs0 hpos hu (ξ := x₀) (not_lt.1 hle)
    exact hbad x' hx' (by rw [hfx']; simp)

/-- **(PC1) for the difference of the means: `R_s = 0` on `ℍ ∖ K_s`.** -/
theorem compFun_eq_zero (hI : IdentHyp W t η p c c₀ v Cv R m f N) {s : ℝ} (hs : s ∈ Ioc 0 t) {y : ℂ}
    (hy : y ∈ H \ fwdHull W s) : compFun W v p c c₀ f s y = 0 := by
  have hW := hI.cont
  have hW0 := hI.zero
  have hv := hI.src
  have hs0 : 0 ≤ s := hs.1.le
  have hsI : s ∈ Icc 0 t := ⟨hs0, hs.2⟩
  have ht : 0 ≤ t := hs0.trans hs.2
  obtain ⟨F, hFeq, hFc, hFR⟩ := exists_extension_of_trace hW hW0 hs0
    (hI.trace_cont.mono (Icc_subset_Icc le_rfl hs.2)) (hI.fill s hs)
  set e := driftGap W v p c with he
  have hec : ContinuousOn e (Icc 0 s) :=
    (continuousOn_driftGap hW ht hv hI.marks).mono (Icc_subset_Icc le_rfl hs.2)
  have hHo : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  have hFΩ : ∀ ξ ∈ H, fwdMapInv W s ξ ∈ H \ fwdHull W s := fun ξ hξ =>
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hs0 hξ
  set Rt : ℂ → ℝ := fun ξ => (flowInt W e s (fwdMapInv W s ξ)).im with hRt
  have hRtF : ∀ ξ ∈ H, Rt ξ = compFun W v p c c₀ f s (F ξ) := fun ξ hξ => by
    rw [hFeq hξ]
    show (flowInt W e s (fwdMapInv W s ξ)).im = _
    rw [im_flowInt hW hs0 hec (hFΩ ξ hξ),
      compFun_eq_integral hW hv hI.marks hI.green hsI (hFΩ ξ hξ)]
  -- harmonic
  have hharm : InnerProductSpace.HarmonicOnNhd Rt H := by
    intro ξ hξ
    have hd : DifferentiableOn ℂ (fun ξ => flowInt W e s (fwdMapInv W s ξ)) H :=
      (differentiableOn_flowInt hW hs0 hec).comp (QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hs0)
        fun ξ hξ => hFΩ ξ hξ
    exact (hd.analyticAt (hHo.mem_nhds hξ)).harmonicAt_im
  -- bounded
  have hbdd : Bornology.IsBounded (Rt '' H) := by
    refine isBounded_iff_forall_norm_le.2 ⟨2 * IsSrc.greenBound Cv R + 2 * (|c₀| + Real.pi * ∑ j, |c j|), ?_⟩
    rintro _ ⟨ξ, hξ, rfl⟩
    rw [Real.norm_eq_abs, hRtF ξ hξ, hFeq hξ]
    exact abs_compFun_le hW hv hI.green hsI (hFΩ ξ hξ)
  -- boundary values
  have hlim : ∀ x : ℝ, x ∉ (∅ : Finset ℝ) → Tendsto (fun ξ => Rt ξ - (fun _ => (0 : ℝ)) ξ)
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
    intro x _
    simp only [sub_zero]
    have hxH : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
    have hFt : Tendsto F (𝓝[H] (x : ℂ)) (𝓝 (F x)) :=
      ((hFc _ hxH).mono QuantumZipper.H_subset_Hbar).tendsto
    have hcongr : (fun ξ => compFun W v p c c₀ f s (F ξ)) =ᶠ[𝓝[H] (x : ℂ)] Rt := by
      filter_upwards [self_mem_nhdsWithin] with ξ hξ using (hRtF ξ hξ).symm
    refine Tendsto.congr' hcongr ?_
    by_cases hA : ∃ a : ℝ, F x = a ∧ ∃ u, IsForwardSol W (a : ℂ) s u
    · -- an alive real point: the integral form
      obtain ⟨a, ha, u, hu⟩ := hA
      have hFt' : Tendsto F (𝓝[H] (x : ℂ)) (𝓝[H \ fwdHull W s] (a : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨ha ▸ hFt, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with ξ hξ
        rw [hFeq hξ]; exact hFΩ ξ hξ
      exact (tendsto_compFun_of_alive hW hv hI.marks hI.green hsI hu).comp hFt'
    · -- otherwise the image lies in `N`
      have hFH : F x ∈ Hbar := by
        have hne : (𝓝[H] (x : ℂ)).NeBot := by
          rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]; exact hxH
        refine (isClosed_le continuous_const Complex.continuous_im).mem_of_tendsto hFt ?_
        filter_upwards [self_mem_nhdsWithin] with ξ hξ
        rw [hFeq hξ]; exact (hFΩ ξ hξ).1.le
      have hKt : fwdHull W s ⊆ closure (fwdHull W t) :=
        (fwdHull_mono' hs.2).trans subset_closure
      have hFN : F x ∈ N := by
        rcases (show (0 : ℝ) ≤ (F x).im from hFH).lt_or_eq with hpos | hzero
        · have hK : F x ∈ fwdHull W s := by
            by_contra hK; exact hFR x (by simp) ⟨hpos, hK⟩
          exact hI.hull_N (hKt hK)
        · have hFx : F x = ((F x).re : ℂ) := Complex.ext (by simp) (by simp [hzero.symm])
          by_cases h0 : (F x).re = 0
          · rw [hFx, h0, Complex.ofReal_zero]; exact hI.zero_N
          · by_cases hcl : F x ∈ closure (fwdHull W s)
            · exact hI.hull_N (closure_mono (fwdHull_mono' hs.2) hcl)
            · exfalso
              obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hcl
              have hd : Disjoint (ball ((F x).re : ℂ) r) (fwdHull W s) := by
                rw [← hFx]
                exact Set.disjoint_left.2 fun z hz hzK => hball hz (subset_closure hzK)
              obtain ⟨u, hu⟩ := ZhanGT4.exists_isForwardSol_of_disjoint_ball hW hW0 h0 hs0 hr hd
              exact hA ⟨(F x).re, hFx, u, hu⟩
      have hstar := star_of_not_alive hI hsI hFeq hFc hA
      have hG := tendsto_greenPot_extension hI hsI hFeq hFc hFN
      have hS := tendsto_argSum_extension hI hsI hFeq hstar
      have hevN : ∀ᶠ ξ in 𝓝[H] (x : ℂ), F ξ ∈ N := hFt (hI.open_N.mem_nhds hFN)
      have heq : (fun ξ => greenPot W v s (F ξ) - argSum W p c c₀ s (F ξ)) =ᶠ[𝓝[H] (x : ℂ)]
          fun ξ => compFun W v p c c₀ f s (F ξ) := by
        filter_upwards [hevN, self_mem_nhdsWithin] with ξ hξN hξ
        have hFξ : F ξ ∈ H := by rw [hFeq hξ]; exact (hFΩ ξ hξ).1
        rw [compFun, hI.f_eq (F ξ) ⟨hξN, hFξ⟩]
        ring
      have := (hG.sub hS)
      rw [sub_zero] at this
      exact this.congr' heq
  have hzero : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => (0 : ℝ)) H := fun w _ =>
    ⟨contDiffAt_const, Filter.Eventually.of_forall fun _ => by simp [InnerProductSpace.laplacian_const]⟩
  have hEq := eqOn_of_tendsto_sub_H ∅ hharm hzero hbdd
    (isBounded_iff_forall_norm_le.2 ⟨0, by rintro _ ⟨w, -, rfl⟩; simp⟩) hlim
  have hfy : fwdMap W s y ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs0 hy
  have h1 := hEq hfy
  rw [hRtF _ hfy, hFeq hfy, QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs0 hy] at h1
  exact h1

/-- **The source drift equals the mark drift** on `[0, t]`: `∫ Im(2/f_u(z)) v(z) dz = ∑ⱼ cⱼ / Re f_u(p_j)`. -/
theorem srcDrift_eq_markDrift (hI : IdentHyp W t η p c c₀ v Cv R m f N) {u : ℝ} (hu : u ∈ Icc 0 t) :
    srcDrift W v u = markDrift W p c u := by
  have hW := hI.cont
  have ht := hI.t_pos
  -- a point alive through `[0, t]`
  obtain ⟨R₁, hR₁, hsub⟩ := (isHPHull_fwdHull hW ht.le).exists_subset_ball
  set y₁ : ℂ := (R₁ : ℂ) * Complex.I with hy₁
  have hy₁t : y₁ ∈ H \ fwdHull W t := by
    refine ⟨show (0 : ℝ) < y₁.im by simp [hy₁, hR₁], fun hK => ?_⟩
    have := hsub hK
    rw [mem_ball, dist_zero_right, hy₁, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR₁] at this
    exact lt_irrefl _ this
  set k : ℝ → ℝ := fun r => (2 / fwdMap W r y₁).im * driftGap W v p c r with hk
  have hkc : ContinuousOn k (Icc 0 t) :=
    (Complex.continuous_im.comp_continuousOn (continuousOn_const.div (Ito.continuousOn_fwdMap_time' hW ht.le hy₁t)
      fun r hr => Ito.fwdMap_ne_zero hW ht.le hy₁t hr)).mul (continuousOn_driftGap hW ht.le hI.src hI.marks)
  have hG0 : ∀ s ∈ Icc (0 : ℝ) t, (∫ r in (0 : ℝ)..s, k r) = 0 := by
    intro s hs
    rcases hs.1.eq_or_lt with h0 | hpos
    · rw [← h0, intervalIntegral.integral_same]
    · rw [← compFun_eq_integral hW hI.src hI.marks hI.green hs (Ito.mem_diff_fwdHull_of_le hy₁t hs.2)]
      exact compFun_eq_zero hI ⟨hpos, hs.2⟩ (Ito.mem_diff_fwdHull_of_le hy₁t hs.2)
  have hd := LocalExt.hasDerivWithinAt_integral_Icc hkc hu
  have hd0 : HasDerivWithinAt (fun s => ∫ r in (0 : ℝ)..s, k r) 0 (Icc 0 t) u :=
    (hasDerivWithinAt_const u (Icc 0 t) (0 : ℝ)).congr (fun s hs => hG0 s hs) (hG0 u hu)
  have hku : k u = 0 := (uniqueDiffOn_Icc ht u hu).eq_deriv _ hd hd0
  have hneg : (2 / fwdMap W u y₁).im < 0 :=
    im_two_div_neg (Ito.im_fwdMap_pos hW ht.le hy₁t hu)
  have : driftGap W v p c u = 0 := by
    rcases mul_eq_zero.1 hku with h | h
    · exact absurd h hneg.ne
    · exact h
  simp only [driftGap] at this
  linarith

end Main

/-! ### The energy of the source drift -/

section Energy

variable {v : ℂ → ℝ} {t Cv R m : ℝ}

/-- **The energy identity** `∫₀ˢ A(u)² du = ∫ v (G_ℍ v − G_{ℍ∖K_s} v)` and its bound by the Green potentials:
`∫₀ˢ A² ≤ 2 CG ∫ |v|` (Hadamard's formula against `v ⊗ v`, Fubini). -/
theorem integral_srcDrift_sq_le (hW : Continuous W) (hv : IsSrc W v t Cv R m) {s : ℝ} (hs : s ∈ Icc 0 t) :
    ∫ u in (0 : ℝ)..s, srcDrift W v u ^ 2 ≤ 2 * IsSrc.greenBound Cv R * ∫ z, |v z| := by
  classical
  have hs0 := hs.1
  have ht : 0 ≤ t := hs0.trans hs.2
  have hcl : ∀ u, LocalExt.clampS s u ∈ Icc 0 t := fun u =>
    ⟨(LocalExt.clampS_mem hs0 u).1, (LocalExt.clampS_mem hs0 u).2.trans hs.2⟩
  obtain ⟨Ca, hCa⟩ := isCompact_Icc.exists_bound_of_continuousOn (hv.continuousOn_srcDrift hW ht)
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (hCa 0 ⟨le_rfl, ht⟩)
  set G : ℝ → ℂ → ℝ := fun u z => IsSrc.srcKer W v (LocalExt.clampS s u) z * v z *
    srcDrift W v (LocalExt.clampS s u) with hG
  have hsc : Continuous fun u => srcDrift W v (LocalExt.clampS s u) :=
    (hv.continuousOn_srcDrift hW ht).comp_continuous (LocalExt.continuous_clampS s) hcl
  have hGm : Measurable fun p : ℝ × ℂ => G p.1 p.2 := by
    refine Coupling.measurable_uncurry_of_continuousOn isClosed_univ (0 : ℝ) (fun z => ?_) (fun u _ => ?_)
      (fun u hu => absurd (mem_univ u) hu)
    · refine Continuous.continuousOn ?_
      have hk : Continuous fun u => IsSrc.srcKer W v (LocalExt.clampS s u) z :=
        (hv.continuousOn_srcKer hW ht z).comp_continuous (LocalExt.continuous_clampS s) hcl
      exact (hk.mul continuous_const).mul hsc
    · exact ((hv.measurable_srcKer hW (hcl u)).mul hv.meas).mul measurable_const
  set K := 2 / m * Cv * Ca with hK
  have hball : Integrable fun z : ℂ => (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  have hGb : ∀ u z, |G u z| ≤ K * (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z := by
    intro u z
    by_cases hz : v z = 0
    · simp only [hG, hz, mul_zero, zero_mul, abs_zero]
      exact mul_nonneg (by have := hv.m_pos; have := hv.Cv_nonneg; positivity)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
    · rw [Set.indicator_of_mem (by rw [mem_closedBall, dist_zero_right]; exact hv.norm_le z hz), mul_one]
      simp only [hG, IsSrc.srcKer, hz, ne_eq, not_false_eq_true, ite_true, abs_mul]
      have h1 := hv.abs_im_two_div_le (hcl u) hz
      have h2 := hv.bound z
      have h3 : |srcDrift W v (LocalExt.clampS s u)| ≤ Ca := by
        have := hCa _ (hcl u); rwa [Real.norm_eq_abs] at this
      have hm2 : 0 ≤ 2 / m := div_nonneg zero_le_two hv.m_pos.le
      have hmC : 0 ≤ 2 / m * Cv := mul_nonneg hm2 hv.Cv_nonneg
      calc |(2 / fwdMap W (LocalExt.clampS s u) z).im| * |v z| * |srcDrift W v (LocalExt.clampS s u)|
          ≤ 2 / m * Cv * Ca := by gcongr
        _ = K := rfl
  have hint : Integrable (Function.uncurry G) ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℂ => (fun _ : ℝ => (1 : ℝ)) p.1 *
        (fun z => K * (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z) p.2)
        ((volume.restrict (uIoc (0 : ℝ) s)).prod volume) := by
      have : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) s)) := by
        rw [uIoc_of_le hs0]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      exact Integrable.mul_prod (L := ℝ) (integrable_const _) (hball.const_mul K)
    refine hg.mono' hGm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, one_mul, Real.norm_eq_abs]
    exact hGb p.1 p.2
  have hswap := intervalIntegral_integral_swap hint
  -- the time side
  have hleft : ∫ u in (0 : ℝ)..s, ∫ z, G u z = ∫ u in (0 : ℝ)..s, srcDrift W v u ^ 2 := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hs0] at hu
    simp only [hG, LocalExt.clampS_of_mem hu, integral_mul_const]
    rw [sq]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun z => IsSrc.srcKer_mul W v u z)
  -- the space side
  have hJ : ∀ z, v z ≠ 0 → ∫ u in (0 : ℝ)..s, G u z = v z * (greenPot0 v z - greenPot W v s z) := by
    intro z hz
    have hzs : z ∈ H \ fwdHull W s := Ito.mem_diff_fwdHull_of_le (hv.alive z hz) hs.2
    have h1 := hv.greenPot_eq hW hs hzs
    have h2 : ∫ u in (0 : ℝ)..s, G u z = v z * ∫ u in (0 : ℝ)..s, (2 / fwdMap W u z).im * srcDrift W v u := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hs0] at hu
      simp only [hG, LocalExt.clampS_of_mem hu, IsSrc.srcKer, hz, ne_eq, not_false_eq_true, ite_true]
      ring
    rw [h2, h1]; ring
  have hFi : Integrable fun z => ∫ u in (0 : ℝ)..s, G u z := by
    refine hint.integral_prod_right.congr (ae_of_all _ fun z => ?_)
    simp only [Function.uncurry, intervalIntegral.integral_of_le hs0, uIoc_of_le hs0]
  rw [← hleft, hswap]
  refine (le_abs_self _).trans ((abs_integral_le_integral_abs).trans ?_)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (hv.integrable.abs.const_mul _)
    (ae_of_all _ fun z => ?_)
  simp only
  by_cases hz : v z = 0
  · have : ∫ u in (0 : ℝ)..s, G u z = 0 := by simp [hG, hz]
    rw [this, abs_zero, hz, abs_zero, mul_zero]
  · have hzs : z ∈ H \ fwdHull W s := Ito.mem_diff_fwdHull_of_le (hv.alive z hz) hs.2
    rw [hJ z hz, abs_mul, mul_comm]
    have h1 := hv.abs_greenPot0_le hzs.1
    have h2 := hv.abs_greenPot_le hW hs hzs
    have h3 : |greenPot0 v z - greenPot W v s z| ≤ 2 * IsSrc.greenBound Cv R := by
      have := abs_sub (greenPot0 v z) (greenPot W v s z); linarith
    exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)

end Energy

end GB7a

end InteractingSLE
