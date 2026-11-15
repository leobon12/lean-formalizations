/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Beta
import InteractingSLE.Spec.Coupling.WholeField9Path
import InteractingSLE.Spec.Coupling.MartMeans2Chart
import InteractingSLE.Spec.Sec7.LocalExtA3Joint

/-!
# Limits in time of the tested coupling mean and of the Green energy

Packet PROVE-STAGEDLAW3. Along stopping times `ρₙ ↑ T` (the stop `T = min t ζ`, reached or announced), the announced
kernel (`WholeField.exists_announced_kernel_history`) has the limit mean `lim (𝔥_{ρₙ}, φ)` and the limit variance
`lim G_{ℍ∖K_{ρₙ}}(φ, φ)`. For a continuous driver on `[0, T]` both limits are the values at `T` (deterministic):

* `exists_pos_le_im_fwdMap`: `Im f_s ≥ δ > 0` on a compact subset of `ℍ ∖ K_T`, uniformly in `s ≤ T` (the imaginary
  part decreases along the flow);
* `norm_logDerivFwd_le`, `continuousOn_logDerivFwd_time`: the canonical `log f_s′` is bounded and continuous in time;
* **`tendsto_integral_couplingMean`**: `∫ 𝔥_{sₙ}^{(uₙ)} φ → ∫ 𝔥_T^{(u)} φ` for `sₙ → T`, harmonic data `uₙ` bounded
  uniformly and converging along the flow (dominated convergence);
* **`tendsto_zeroGFFTestCov_time`**: `G_{ℍ∖K_{sₙ}}(φ, φ) → G_{ℍ∖K_T}(φ, φ)` (Wang–Wu's continuity of the retained Green
  form, `WholeField.continuous_retainedGreenForm_min_of_path`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper LQGMetric

section Lim

variable {w : ℝ → ℝ} {T : ℝ}

theorem fwdHull_subset_of_le {s t : ℝ} (h : s ≤ t) : fwdHull w s ⊆ fwdHull w t :=
  fun _ hz => ⟨hz.1, hz.2.trans (ENNReal.ofReal_le_ofReal h)⟩

/-- **A uniform lower bound for `Im f_s` on a compact subset of the domain at `T`, for all `s ≤ T`.** -/
theorem exists_pos_le_im_fwdMap (hw : Continuous w) (hT : 0 ≤ T) {K : Set ℂ} (hK : IsCompact K)
    (hKD : K ⊆ H \ fwdHull w T) : ∃ δ > 0, ∀ z ∈ K, ∀ s ∈ Icc 0 T, δ ≤ (fwdMap w s z).im := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact absurd hz (notMem_empty z)⟩
  have hcont : ContinuousOn (fun z => (fwdMap w T z).im) K :=
    Complex.continuous_im.comp_continuousOn ((FwdHolo.differentiableOn_fwdMap hw hT).continuousOn.mono hKD)
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hcont
  refine ⟨(fwdMap w T z₀).im, (RS.im_fwdMap_le_of_le hw hT le_rfl (hKD hz₀)).2, fun z hz s hs => ?_⟩
  exact (hmin hz).trans (RS.im_fwdMap_le_of_le hw hs.1 hs.2 (hKD hz)).1

/-- The canonical `log f_s′` is bounded on `[0, T]` by `2T/δ²`. -/
theorem norm_logDerivFwd_le {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hlow : ∀ s ∈ Icc 0 T, δ ≤ (fwdMap w s z).im) {s : ℝ}
    (hs : s ∈ Icc 0 T) : ‖logDerivFwd w s z‖ ≤ 2 / δ ^ 2 * T := by
  unfold logDerivFwd
  rw [norm_neg]
  have h : ∀ r ∈ Set.uIoc (0 : ℝ) s, ‖2 / (fwdMap w r z) ^ 2‖ ≤ 2 / δ ^ 2 := by
    intro r hr
    rw [uIoc_of_le hs.1] at hr
    have hδr := hlow r ⟨hr.1.le, hr.2.trans hs.2⟩
    have hn : δ ≤ ‖fwdMap w r z‖ := hδr.trans (Complex.im_le_norm _)
    rw [norm_div, norm_pow, Complex.norm_two]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hδ.le hn 2)
  refine (intervalIntegral.norm_integral_le_of_norm_le_const h).trans ?_
  rw [sub_zero, abs_of_nonneg hs.1]
  exact mul_le_mul_of_nonneg_left hs.2 (by positivity)

/-- The canonical `log f_s′(z)` is continuous in `s ∈ [0, T]` for `z ∈ ℍ ∖ K_T`. -/
theorem continuousOn_logDerivFwd_time (hw : Continuous w) (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ H \ fwdHull w T) :
    ContinuousOn (fun s => logDerivFwd w s z) (Icc 0 T) := by
  have hf := FwdHolo.continuousOn_fwdMap_time hw hT hz
  have hne : ∀ s ∈ Icc (0 : ℝ) T, fwdMap w s z ≠ 0 := fun s hs h0 => by
    have := (RS.im_fwdMap_le_of_le hw hs.1 hs.2 hz).1
    have h2 := (RS.im_fwdMap_le_of_le hw hT le_rfl hz).2
    rw [h0, Complex.zero_im] at this
    linarith
  have hg : ContinuousOn (fun r => 2 / (fwdMap w r z) ^ 2) (Icc 0 T) :=
    continuousOn_const.div (hf.pow 2) fun r hr => pow_ne_zero 2 (hne r hr)
  have hI : IntegrableOn (fun r => 2 / (fwdMap w r z) ^ 2) (uIcc 0 T) volume := by
    rw [uIcc_of_le hT]
    exact hg.integrableOn_compact isCompact_Icc
  have hp := intervalIntegral.continuousOn_primitive_interval (μ := volume) hI
  rw [uIcc_of_le hT] at hp
  exact hp.neg

/-- **The tested coupling mean converges in time** to its value at `T`. -/
theorem tendsto_integral_couplingMean (κ : ℝ) (hw : Continuous w) (hT : 0 ≤ T) {s : ℕ → ℝ}
    (hs : ∀ n, s n ∈ Icc 0 T) (hsT : Tendsto s atTop (𝓝 T)) {u : ℕ → ℂ → ℝ} {u' : ℂ → ℝ} {C : ℝ}
    (huc : ∀ n, ContinuousOn (u n) H) (hub : ∀ n y, |u n y| ≤ C) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : tsupport ψ ⊆ H \ fwdHull w T)
    (hlim : ∀ z ∈ tsupport ψ, Tendsto (fun n => u n (fwdMap w (s n) z)) atTop (𝓝 (u' (fwdMap w T z)))) :
    Tendsto (fun n => ∫ z, couplingMean κ w (s n) (u n) z * ψ z) atTop
      (𝓝 (∫ z, couplingMean κ w T u' z * ψ z)) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (hub 0 0)
  obtain ⟨δ, hδ, hlow⟩ := exists_pos_le_im_fwdMap hw hT (ψ.hasCompactSupport.isCompact) hψ
  set B : ℝ := C + |chiC κ| * (2 / δ ^ 2 * T) with hBdef
  have hB : 0 ≤ B := add_nonneg hC (mul_nonneg (abs_nonneg _) (by positivity))
  have hψi : Integrable fun z => ψ z := ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  refine tendsto_integral_of_dominated_convergence (fun z => B * |ψ z|) (fun n => ?_)
    (hψi.abs.const_mul B) (fun n => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => ?_)
  · have hsub : tsupport ψ ⊆ H \ fwdHull w (s n) :=
      hψ.trans (sdiff_subset_sdiff_right (fwdHull_subset_of_le (hs n).2))
    exact (Coupling.MartMeans2.integrable_mul_test_of_continuousOn
      (LocalExt.continuousOn_couplingMean_alive hw (hs n).1 (huc n)) ψ hsub).aestronglyMeasurable
  · by_cases hz : z ∈ tsupport ψ
    · have hL := norm_logDerivFwd_le hδ (hlow z hz) (hs n)
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      unfold couplingMean
      refine (abs_sub _ _).trans (add_le_add (hub n _) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans hL) (abs_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, norm_zero, abs_zero, mul_zero]
  · by_cases hz : z ∈ tsupport ψ
    · refine Tendsto.mul_const _ ?_
      unfold couplingMean
      refine (hlim z hz).sub (Tendsto.const_mul _ ?_)
      have hc := (continuousOn_logDerivFwd_time hw hT (hψ hz)) T ⟨hT, le_rfl⟩
      have hst : Tendsto s atTop (𝓝[Icc 0 T] T) := tendsto_nhdsWithin_iff.2 ⟨hsT, Eventually.of_forall hs⟩
      exact (Complex.continuous_im.tendsto _).comp (hc.tendsto.comp hst)
    · simp only [image_eq_zero_of_notMem_tsupport hz, mul_zero]
      exact tendsto_const_nhds

end Lim

/-- **The Green energy of the remaining domain converges in time** to its value at `T` (continuous driver). -/
theorem tendsto_zeroGFFTestCov_time {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ≥0}
    {s : ℕ → ℝ≥0} (hs : ∀ n, s n ≤ T) (hsT : Tendsto s atTop (𝓝 T)) (ψ : TestOn upperHalfPlaneOpens)
    (hψ : Disjoint (tsupport ψ) (fwdHull (Ito.rpath w) T)) :
    Tendsto (fun n => zeroGFFTestCov (H \ fwdHull (Ito.rpath w) (s n)) ψ ψ) atTop
      (𝓝 (zeroGFFTestCov (H \ fwdHull (Ito.rpath w) T) ψ ψ)) := by
  have hc : ContinuousOn w {t | (t : ℝ≥0∞) < ⊤} := hw.continuousOn
  have e : ∀ r : ℝ≥0, r ≤ T →
      zeroGFFTestCov (H \ fwdHull (Ito.rpath w) r) ψ ψ = WangWu.retainedGreenForm w (min r T) ψ ψ := by
    intro r hr
    have hd : Disjoint (tsupport ψ) (fwdHull (Ito.rpath w) r) :=
      hψ.mono_right (fwdHull_subset_of_le (by exact_mod_cast hr))
    rw [min_eq_left hr]
    have h1 := WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov hc hw0 (ENNReal.coe_lt_top (r := r)) ψ hd
    have h2 := WholeField.retainedGreenEnergy_eq_loewnerGreenEnergy_of_path hc hw0
      (ENNReal.coe_lt_top (r := r)) ψ.tsupport_subset hd
    rw [← WangWu.retainedGreenEnergy_eq_form]
    exact h1.symm.trans h2.symm
  have hcont := WholeField.continuous_retainedGreenForm_min_of_path hc hw0 (σ := T) ENNReal.coe_lt_top
    (WholeField.isTestFn_of_testOn ψ) (WholeField.isTestFn_of_testOn ψ)
  have hlim := (hcont.tendsto T).comp hsT
  rw [min_self] at hlim
  rw [e T le_rfl, min_self]
  exact hlim.congr fun n => (e (s n) (hs n)).symm

end StagedLaw

end Exist

end InteractingSLE
