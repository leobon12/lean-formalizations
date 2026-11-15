/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux61Mean
import InteractingSLE.Foundations.Loewner.YuanTrace

/-!
# Aux. lemma 61, deterministic layer: tools for the harmonic uniqueness argument

Packet PROVE-GB7A2. Generic facts used in the proof of the drift identity (`Aux61Ident`):

* `differentiableOn_flowInt`: `y ↦ ∫₀ˢ 2 e(u)/f_u(y) du` is holomorphic on `ℍ ∖ K_s` for a continuous `e` (the
  argument of `LocalExt.differentiableOn_phiFun` for a general coefficient);
* `greenH_le_of_mem_H`, `IsSrc.exists_bound_integral_abs_greenH`, `IsSrc.abs_greenPot_le`: the Green function of `ℍ`
  is at most `2 Im a Im b/|a − b|²`, and the Green potentials of a source are uniformly bounded;
* `exists_extension_of_trace`: a continuous trace generating the hulls up to time `s` gives the continuous boundary
  extension of `F_s = f_s⁻¹` to `ℍ̄` (YuanTrace's `IsLoewnerTrace.exists_extension` with hypotheses at one time);
* `extension_fwdMap_real`: the extension maps the image of an alive real point back to it;
* `exists_fwdMap_real_eq_of_le`, `exists_fwdMap_real_eq_of_ge_neg`: the real flow at time `s` maps the alive half-
  lines beyond a mark onto the half-lines beyond its image (intermediate values).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal ComplexConjugate Interval

namespace InteractingSLE

namespace GB7a

open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol greenH fwdMapInv)
open SupercriticalConformalCovariance (IsConformalBijection)

variable {W : ℝ → ℝ}

/-! ### A holomorphic parametric integral -/

/-- `Φ_s(y) = ∫₀ˢ 2 e(u)/f_u(y) du`. -/
def flowInt (W : ℝ → ℝ) (e : ℝ → ℝ) (s : ℝ) (y : ℂ) : ℂ := ∫ u in (0 : ℝ)..s, 2 * (e u : ℂ) / fwdMap W u y

theorem im_flowInt (hW : Continuous W) {e : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s) (he : ContinuousOn e (Icc 0 s))
    {y : ℂ} (hy : y ∈ H \ fwdHull W s) :
    (flowInt W e s y).im = ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * e u := by
  have hcont : ContinuousOn (fun u => 2 * (e u : ℂ) / fwdMap W u y) (Icc 0 s) :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn he)).div
      (Ito.continuousOn_fwdMap_time' hW hs hy) fun u hu => Ito.fwdMap_ne_zero hW hs hy hu
  rw [flowInt, ← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _
    (hcont.intervalIntegrable_of_Icc hs)]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [Complex.imCLM_apply]
  rw [show 2 * (e u : ℂ) / fwdMap W u y = (e u : ℂ) * (2 / fwdMap W u y) by ring, Complex.im_ofReal_mul]
  ring

/-- **`Φ_s` is holomorphic on `ℍ ∖ K_s`** (differentiation under the integral: on a closed disc around a point
of `ℍ ∖ K_s`, `|f_u| ≥ Im f_s ≥ δ > 0` for `u ≤ s`, so the `y`-derivative `−2e(u) f_u'(y)/f_u(y)²` is bounded). -/
theorem differentiableOn_flowInt (hW : Continuous W) {e : ℝ → ℝ} {s : ℝ} (hs0 : 0 ≤ s)
    (he : ContinuousOn e (Icc 0 s)) : DifferentiableOn ℂ (flowInt W e s) (H \ fwdHull W s) := by
  intro y₀ hy₀
  have hopen := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs0
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 hopen y₀ hy₀
  set B := closedBall y₀ (ρ / 2) with hB
  have hBsub : B ⊆ H \ fwdHull W s := (closedBall_subset_ball (by linarith)).trans hball
  have hcont_im : ContinuousOn (fun y => (fwdMap W s y).im) B :=
    Complex.continuous_im.comp_continuousOn
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs0).continuousOn.mono hBsub)
  obtain ⟨y₁, hy₁B, hy₁⟩ := (isCompact_closedBall y₀ (ρ / 2)).exists_isMinOn
    ⟨y₀, mem_closedBall_self (by linarith)⟩ hcont_im
  set δ := (fwdMap W s y₁).im with hδ
  have hδpos : 0 < δ := Ito.im_fwdMap_pos hW hs0 (hBsub hy₁B) ⟨hs0, le_rfl⟩
  have hlow : ∀ y ∈ B, ∀ u ∈ Icc (0 : ℝ) s, δ ≤ ‖fwdMap W u y‖ := fun y hy u hu => by
    have h1 : δ ≤ (fwdMap W s y).im := hy₁ hy
    have hanti := (QuantumZipper.im_isForwardSol_le hW (hBsub hy).1
      (Ito.isForwardSol_fwdMap_of_mem hW hs0 (hBsub hy))).1 hu ⟨hs0, le_rfl⟩ hu.2
    exact h1.trans (hanti.trans ((le_abs_self _).trans (Complex.abs_im_le_norm _)))
  obtain ⟨Cc, hCc⟩ := isCompact_Icc.exists_bound_of_continuousOn he
  have hCc0 : 0 ≤ Cc := (norm_nonneg _).trans (hCc 0 ⟨le_rfl, hs0⟩)
  let F : ℂ → ℝ → ℂ := fun y u => 2 * (e u : ℂ) / fwdMap W u y
  let F' : ℂ → ℝ → ℂ := fun y u => -(2 * (e u : ℂ) *
    Complex.exp (QuantumZipper.logDerivFwd W u y) / fwdMap W u y ^ 2)
  have hIoc : Ι (0 : ℝ) s = Ioc 0 s := uIoc_of_le hs0
  have hFc : ∀ y ∈ H \ fwdHull W s, ContinuousOn (F y) (Icc 0 s) := fun y hy =>
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn he)).div
      (Ito.continuousOn_fwdMap_time' hW hs0 hy) fun u hu => Ito.fwdMap_ne_zero hW hs0 hy hu
  have hF'c : ContinuousOn (F' y₀) (Icc 0 s) :=
    (((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn he)).mul
      (Complex.continuous_exp.comp_continuousOn (Ito.continuousOn_logDerivFwd hW hs0 hy₀))).div
      ((Ito.continuousOn_fwdMap_time' hW hs0 hy₀).pow 2) fun u hu =>
        pow_ne_zero 2 (Ito.fwdMap_ne_zero hW hs0 hy₀ hu)).neg
  have hmeas : ∀ {g : ℝ → ℂ}, ContinuousOn g (Icc 0 s) →
      AEStronglyMeasurable g (volume.restrict (Ι (0 : ℝ) s)) := fun hg => by
    rw [hIoc]; exact (hg.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  set K := 2 * Cc * Real.exp (2 * s / δ ^ 2) / δ ^ 2 with hK
  have hbound : ∀ᵐ u ∂(volume.restrict (Ι (0 : ℝ) s)), ∀ y ∈ B, ‖F' y u‖ ≤ K := by
    rw [hIoc]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun u hu y hy => ?_)
    have huI : u ∈ Icc 0 s := Ioc_subset_Icc_self hu
    have hL : ‖QuantumZipper.logDerivFwd W u y‖ ≤ 2 * s / δ ^ 2 := by
      rw [QuantumZipper.logDerivFwd, norm_neg]
      have hb : ∀ r ∈ Ι (0 : ℝ) u, ‖2 / fwdMap W r y ^ 2‖ ≤ 2 / δ ^ 2 := fun r hr => by
        rw [uIoc_of_le huI.1] at hr
        have hrI : r ∈ Icc 0 s := ⟨hr.1.le, hr.2.trans huI.2⟩
        rw [norm_div, norm_pow]
        simp only [Complex.norm_ofNat]
        exact div_le_div_of_nonneg_left zero_le_two (by positivity)
          (pow_le_pow_left₀ hδpos.le (hlow y hy r hrI) 2)
      have := intervalIntegral.norm_integral_le_of_norm_le_const hb
      rw [sub_zero, abs_of_nonneg huI.1] at this
      have hus : 2 / δ ^ 2 * u ≤ 2 / δ ^ 2 * s := mul_le_mul_of_nonneg_left huI.2 (by positivity)
      calc ‖∫ r in (0 : ℝ)..u, 2 / fwdMap W r y ^ 2‖ ≤ 2 / δ ^ 2 * u := this
        _ ≤ 2 / δ ^ 2 * s := hus
        _ = 2 * s / δ ^ 2 := by ring
    have hexp : ‖Complex.exp (QuantumZipper.logDerivFwd W u y)‖ ≤ Real.exp (2 * s / δ ^ 2) := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans hL)
    show ‖-(2 * (e u : ℂ) * Complex.exp (QuantumZipper.logDerivFwd W u y) / fwdMap W u y ^ 2)‖ ≤ K
    simp only [norm_neg, norm_div, norm_mul, norm_pow]
    have h2c : ‖(2 : ℂ)‖ * ‖(e u : ℂ)‖ ≤ 2 * Cc := by
      rw [Complex.norm_ofNat, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left (hCc u huI) zero_le_two
    have hfn := hlow y hy u huI
    calc ‖(2 : ℂ)‖ * ‖(e u : ℂ)‖ * ‖Complex.exp (QuantumZipper.logDerivFwd W u y)‖ / ‖fwdMap W u y‖ ^ 2
        ≤ 2 * Cc * Real.exp (2 * s / δ ^ 2) / δ ^ 2 := by gcongr
      _ = K := rfl
  have hdiff : ∀ᵐ u ∂(volume.restrict (Ι (0 : ℝ) s)), ∀ y ∈ B, HasDerivAt (F · u) (F' y u) y := by
    rw [hIoc]
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun u hu y hy => ?_)
    have huI : u ∈ Icc 0 s := Ioc_subset_Icc_self hu
    have hyu := Ito.mem_diff_fwdHull_of_le (hBsub hy) huI.2
    have hd := QuantumZipper.FwdHolo.hasDerivAt_fwdMap hW huI.1 hyu
    have hne := Ito.fwdMap_ne_zero hW huI.1 hyu ⟨huI.1, le_rfl⟩
    have := (hasDerivAt_const y (2 * (e u : ℂ))).div hd hne
    refine this.congr_deriv ?_
    show _ = -(2 * (e u : ℂ) * Complex.exp (QuantumZipper.logDerivFwd W u y) / fwdMap W u y ^ 2)
    ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ι (0 : ℝ) s))
    (F := F) (F' := F') (x₀ := y₀) (bound := fun _ => K) (closedBall_mem_nhds y₀ (by linarith))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds y₀ hρ) fun y hy => hmeas (hFc y (hball hy))) ?_
    (hmeas hF'c) hbound ?_ hdiff
  · have heq : flowInt W e s = fun y => ∫ u, F y u ∂(volume.restrict (Ι (0 : ℝ) s)) := by
      funext y
      rw [flowInt, intervalIntegral.integral_of_le hs0, hIoc]
    rw [heq]
    exact hres.2.differentiableAt.differentiableWithinAt
  · rw [hIoc]; exact (hFc y₀ hy₀).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  · have : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) s)) := by
      rw [hIoc]; exact isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    exact integrable_const K

/-! ### Bounds on the Green function of `ℍ` -/

theorem norm_sub_conj_sq (a b : ℂ) : ‖a - conj b‖ ^ 2 = ‖a - b‖ ^ 2 + 4 * a.im * b.im := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.conj_re, Complex.sub_im, Complex.conj_im]
  ring

/-- `G_ℍ(a, b) ≤ 2 Im a Im b / |a − b|²` for `a ≠ b` in `ℍ`. -/
theorem greenH_le_of_mem_H {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (hab : a ≠ b) :
    greenH a b ≤ 2 * a.im * b.im / ‖a - b‖ ^ 2 := by
  have h1 : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  have h2 : 0 < ‖a - conj b‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hq : 0 < ‖a - conj b‖ ^ 2 / ‖a - b‖ ^ 2 := by positivity
  have hlog : 2 * greenH a b = Real.log (‖a - conj b‖ ^ 2 / ‖a - b‖ ^ 2) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow, greenH]
    push_cast; ring
  have hle := Real.log_le_sub_one_of_pos hq
  rw [norm_sub_conj_sq, add_div, div_self (by positivity)] at hle hlog
  have h4 : 4 * a.im * b.im / ‖a - b‖ ^ 2 = 2 * (2 * a.im * b.im / ‖a - b‖ ^ 2) := by ring
  linarith

/-- `Im(2/w) < 0` on `ℍ`. -/
theorem im_two_div_neg {w : ℂ} (hw : 0 < w.im) : (2 / w).im < 0 := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_im] at hw; exact lt_irrefl 0 hw
  rw [div_eq_mul_inv, Complex.mul_im, Complex.inv_im, Complex.inv_re]
  simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
  have : 0 < Complex.normSq w := Complex.normSq_pos.2 hw0
  have : 0 < w.im / Complex.normSq w := div_pos hw this
  rw [neg_div]
  linarith

/-- The Green function decreases along the flow: `0 ≤ G_ℍ(f_s y, f_s z) ≤ G_ℍ(y, z)`. -/
theorem greenH_fwdMap_le (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) {y z : ℂ} (hy : y ∈ H \ fwdHull W s)
    (hz : z ∈ H \ fwdHull W s) (hyz : y ≠ z) :
    0 ≤ greenH (fwdMap W s y) (fwdMap W s z) ∧ greenH (fwdMap W s y) (fwdMap W s z) ≤ greenH y z := by
  constructor
  · have hfy : 0 < (fwdMap W s y).im := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hy
    have hfz : 0 < (fwdMap W s z).im := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hz
    refine QuantumZipper.greenH_nonneg (show fwdMap W s y ∈ Hbar from hfy.le)
      (show fwdMap W s z ∈ Hbar from hfz.le) fun h => hyz ?_
    exact QuantumZipper.FwdHolo.injOn_fwdMap hW hs hy hz h
  · rw [Ito.greenH_fwdMap_eq_sub_integral hW hs hy hz hyz]
    have : 0 ≤ ∫ u in (0 : ℝ)..s, (2 / fwdMap W u y).im * (2 / fwdMap W u z).im := by
      refine intervalIntegral.integral_nonneg hs fun u hu => ?_
      exact mul_nonneg_of_nonpos_of_nonpos
        (im_two_div_neg (Ito.im_fwdMap_pos hW hs hy hu)).le (im_two_div_neg (Ito.im_fwdMap_pos hW hs hz hu)).le
    linarith

/-- The logarithmic singularity, restricted to the unit disc. -/
def logBump (w : ℂ) : ℝ := (closedBall (0 : ℂ) 1).indicator (fun w => |Real.log ‖w‖|) w

theorem logBump_nonneg (w : ℂ) : 0 ≤ logBump w :=
  Set.indicator_nonneg (fun _ _ => abs_nonneg _) w

theorem integrable_logBump : Integrable logBump := by
  obtain ⟨ψ, hψc, hψs, hψ0, hψ1⟩ := IsSrc.exists_bump 1
  have hi := (QuantumZipper.K3.integrable_log_norm_sub_mul_K3 hψc hψs 0).abs
  have hm : Measurable logBump :=
    (continuous_abs.measurable.comp (measurable_norm.log)).indicator measurableSet_closedBall
  refine hi.mono' hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (logBump_nonneg w), logBump]
  by_cases hw : w ∈ closedBall (0 : ℂ) 1
  · rw [Set.indicator_of_mem hw, sub_zero, hψ1 w (by rwa [mem_closedBall, dist_zero_right] at hw), mul_one]
  · rw [Set.indicator_of_notMem hw]; exact abs_nonneg _

/-- `G_ℍ(y, z) ≤ log(1 + 2R) + logBump(z − y)` for `y, z ∈ ℍ`, `‖z‖ ≤ R`, `y ≠ z`. -/
theorem greenH_le_log_add {y z : ℂ} (hy : 0 < y.im) (hz : 0 < z.im) {R : ℝ} (hzR : ‖z‖ ≤ R) (hyz : y ≠ z) :
    greenH y z ≤ Real.log (1 + 2 * R) + logBump (z - y) := by
  set r := ‖y - z‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hyz)
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hzR
  have hA : ‖y - conj z‖ ≤ r + 2 * R := by
    have h1 : ‖y - conj z‖ ≤ ‖y - z‖ + ‖z - conj z‖ := by
      have := norm_add_le (y - z) (z - conj z); rwa [sub_add_sub_cancel] at this
    have h2 : ‖z - conj z‖ ≤ 2 * R := by
      have : z - conj z = (2 * z.im : ℝ) * Complex.I := by
        apply Complex.ext <;> simp; ring
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith [(Complex.abs_im_le_norm z).trans' (le_abs_self z.im)]
    linarith
  have hA0 : 0 < ‖y - conj z‖ := by
    refine norm_pos_iff.2 fun h0 => ?_
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have hg : greenH y z ≤ Real.log (r + 2 * R) - Real.log r := by
    rw [greenH]
    exact sub_le_sub_right (Real.log_le_log hA0 hA) _
  have hzy : ‖z - y‖ = r := norm_sub_rev z y
  rcases le_or_gt 1 r with h1 | h1
  · have : Real.log (r + 2 * R) - Real.log r ≤ Real.log (1 + 2 * R) := by
      rw [← Real.log_div (by linarith) hr0.ne']
      refine Real.log_le_log (by positivity) ?_
      rw [div_le_iff₀ hr0]; nlinarith
    linarith [logBump_nonneg (z - y)]
  · have hb : logBump (z - y) = -Real.log r := by
      rw [logBump, Set.indicator_of_mem (by rw [mem_closedBall, dist_zero_right, hzy]; exact h1.le), hzy,
        abs_of_nonpos (Real.log_nonpos hr0.le h1.le)]
    rw [hb]
    have : Real.log (r + 2 * R) ≤ Real.log (1 + 2 * R) := Real.log_le_log (by linarith) (by linarith)
    linarith

namespace IsSrc

variable {v : ℂ → ℝ} {t Cv R m : ℝ}

/-- **The uniform bound for Green potentials of a source**: `∫ |G_ℍ(y, z) v(z)| dz ≤ CG` for every `y ∈ ℍ`. -/
theorem integral_abs_greenH_mul_le (h : IsSrc W v t Cv R m) {y : ℂ} (hy : 0 < y.im) :
    ∫ z, |greenH y z * v z| ≤
      Cv * (Real.log (1 + 2 * R) * (volume (closedBall (0 : ℂ) R)).toReal + ∫ w, logBump w) := by
  have hball : Integrable fun z : ℂ => (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  have hlb : Integrable fun z => logBump (z - y) := integrable_logBump.comp_sub_right y
  have hg : Integrable fun z => Cv * (Real.log (1 + 2 * R) * (closedBall (0 : ℂ) R).indicator
      (fun _ => (1 : ℝ)) z + logBump (z - y)) := ((hball.const_mul _).add hlb).const_mul Cv
  have hbd : (fun z => |greenH y z * v z|) ≤ᵐ[volume] fun z => Cv * (Real.log (1 + 2 * R) *
      (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z + logBump (z - y)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton y)] with z hzy
    by_cases hz : v z = 0
    · rw [hz, mul_zero, abs_zero]
      have hR : 0 ≤ Real.log (1 + 2 * R) * (closedBall (0 : ℂ) R).indicator (fun _ => (1 : ℝ)) z := by
        by_cases hzb : z ∈ closedBall (0 : ℂ) R
        · rw [Set.indicator_of_mem hzb, mul_one]
          have hzR' : ‖z‖ ≤ R := by rw [mem_closedBall, dist_zero_right] at hzb; exact hzb
          exact Real.log_nonneg (by linarith [norm_nonneg z])
        · rw [Set.indicator_of_notMem hzb, mul_zero]
      exact mul_nonneg h.Cv_nonneg (add_nonneg hR (logBump_nonneg _))
    · have hzH : 0 < z.im := (h.alive z hz).1
      have hzR := h.norm_le z hz
      have hR0 : 0 ≤ R := (norm_nonneg _).trans hzR
      have hg0 : 0 ≤ greenH y z := QuantumZipper.greenH_nonneg (show y ∈ Hbar from hy.le)
        (show z ∈ Hbar from hzH.le) (Ne.symm hzy)
      rw [Set.indicator_of_mem (by rwa [mem_closedBall, dist_zero_right]), mul_one, abs_mul,
        abs_of_nonneg hg0, mul_comm]
      exact mul_le_mul (h.bound z) (greenH_le_log_add hy hzH hzR (Ne.symm hzy)) hg0 h.Cv_nonneg
  refine (integral_mono_ae (h.integrable_greenH_mul y).abs hg hbd).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add (hball.const_mul _) hlb, integral_const_mul,
    integral_sub_right_eq_self (fun w => logBump w) y, integral_indicator measurableSet_closedBall,
    setIntegral_const, smul_eq_mul, mul_one, measureReal_def]

/-- The constant of the Green-potential bound. -/
def greenBound (Cv R : ℝ) : ℝ :=
  Cv * (Real.log (1 + 2 * R) * (volume (closedBall (0 : ℂ) R)).toReal + ∫ w, logBump w)

theorem abs_greenPot0_le (h : IsSrc W v t Cv R m) {y : ℂ} (hy : 0 < y.im) :
    |greenPot0 v y| ≤ greenBound Cv R :=
  (abs_integral_le_integral_abs).trans (h.integral_abs_greenH_mul_le hy)

theorem abs_greenPot_le (h : IsSrc W v t Cv R m) (hW : Continuous W) {s : ℝ} (hs : s ∈ Icc 0 t) {y : ℂ}
    (hy : y ∈ H \ fwdHull W s) : |greenPot W v s y| ≤ greenBound Cv R := by
  have h1 : |greenPot W v s y| ≤ ∫ z, |greenH (fwdMap W s y) (fwdMap W s z) * v z| := by
    rw [greenPot, ← Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (fun z => greenH (fwdMap W s y) (fwdMap W s z) * v z)
  refine h1.trans ((integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
    (h.integrable_greenH_mul y).abs ?_).trans (h.integral_abs_greenH_mul_le hy.1))
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton y)] with z hzy
  by_cases hz : v z = 0
  · simp [hz]
  · have hzs : z ∈ H \ fwdHull W s := Ito.mem_diff_fwdHull_of_le (h.alive z hz) hs.2
    obtain ⟨hg0, hgle⟩ := greenH_fwdMap_le hW hs.1 hy hzs (Ne.symm hzy)
    have hy1 : 0 < y.im := hy.1
    have hz1 : 0 < z.im := hzs.1
    have hg0' : 0 ≤ greenH y z := QuantumZipper.greenH_nonneg (show y ∈ Hbar from hy1.le)
      (show z ∈ Hbar from hz1.le) (Ne.symm hzy)
    rw [abs_mul, abs_mul, abs_of_nonneg hg0, abs_of_nonneg hg0']
    exact mul_le_mul_of_nonneg_right hgle (abs_nonneg _)

end IsSrc

/-! ### The boundary extension of `F_s` from a trace -/

/-- **The boundary extension of `F_s = f_s⁻¹`** from a continuous trace generating the hull at time `s`
(YuanTrace's `IsLoewnerTrace.exists_extension`, with its hypotheses at the single time `s`). -/
theorem exists_extension_of_trace (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {η : ℝ → ℂ}
    (hηc : ContinuousOn η (Icc 0 s)) (hfill : fwdHull W s = fillH (η '' Icc 0 s)) :
    ∃ F : ℂ → ℂ, EqOn F (fwdMapInv W s) H ∧ ContinuousOn F Hbar ∧
      ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull W s := by
  set γ : ℝ → ℂ := fun r => clipH (η r) with hγ
  have hγc : ContinuousOn γ (Icc 0 s) := continuous_clipH.comp_continuousOn hηc
  have hγH : MapsTo γ (Icc 0 s) Hbar := fun r _ => clipH_mem_Hbar _
  have hηcpt : IsCompact (η '' Icc 0 s) := isCompact_Icc.image_of_continuousOn hηc
  have hfill' : fillH (γ '' Icc 0 s) = fwdHull W s := by
    rw [hfill]
    apply fillH_congr
    have hc1 : IsCompact (γ '' Icc 0 s) := isCompact_Icc.image_of_continuousOn hγc
    rw [hc1.isClosed.closure_eq, hηcpt.isClosed.closure_eq]
    rw [show γ '' Icc 0 s = clipH '' (η '' Icc 0 s) from (image_image clipH η _).symm]
    exact image_clipH_inter_H _
  have hψ : IsConformalBijection (fwdMapInv W s) H (H \ fillH (γ '' Icc 0 s)) := by
    rw [hfill']; exact isConformalBijection_fwdMapInv hW hW0 hs
  obtain ⟨F, hFeq, hFc, hFfr, -⟩ := exists_continuousOn_extension_of_path_of_tendsto hγc hγH hψ
    (tendsto_fwdMapInv_cobounded hW hW0 hs)
  refine ⟨F, hFeq, hFc, fun x hx hFx => ?_⟩
  have hxH : x ∈ Hbar \ H := ⟨mem_Hbar_of_im_eq_zero hx, fun h => by
    have : (0 : ℝ) < x.im := h
    rw [hx] at this; exact lt_irrefl 0 this⟩
  have hfr := hFfr hxH
  rw [hfill', (isHPHull_fwdHull hW hs).isOpen.frontier_eq] at hfr
  exact hfr.2 hFx

/-- **The extension maps the image of an alive real point back to it**: `F̄_s(f_s(x)) = x`. -/
theorem extension_fwdMap_real (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {F : ℂ → ℂ}
    (hFeq : EqOn F (fwdMapInv W s) H) (hFc : ContinuousOn F Hbar) {x : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) s u) : F (fwdMap W s x) = x := by
  have hlim := tendsto_fwdMap_of_isForwardSol hW hs hu
  rw [← fwdMap_eq_of_isForwardSol hW hu ⟨hs, le_rfl⟩] at hlim
  -- points of `ℍ` near `x` are alive
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hs hu
  have halive : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H \ fwdHull W s := by
    have hE : 0 < Real.exp (2 / δ ^ 2 * s) := Real.exp_pos _
    have hball : ∀ᶠ z : ℂ in 𝓝 (x : ℂ), ‖z - (x : ℂ)‖ * Real.exp (2 / δ ^ 2 * s) < δ := by
      have hc : Continuous fun z : ℂ => ‖z - (x : ℂ)‖ * Real.exp (2 / δ ^ 2 * s) :=
        (continuous_norm.comp (continuous_id.sub continuous_const)).mul continuous_const
      have h0 : ‖(x : ℂ) - (x : ℂ)‖ * Real.exp (2 / δ ^ 2 * s) < δ := by simpa using hδ
      exact hc.continuousAt.eventually (gt_mem_nhds h0)
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hz hzH
    exact ⟨hzH, not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hzH hz⟩
  have hxHbar : fwdMap W s x ∈ Hbar := by
    show 0 ≤ (fwdMap W s x).im
    rw [im_fwdMap_real_eq_zero hW hu ⟨hs, le_rfl⟩]
  -- `F ∘ f_s → F(f_s x)` and `F ∘ f_s = id` near `x`
  have hmaps : ∀ᶠ z in 𝓝[H] (x : ℂ), fwdMap W s z ∈ Hbar := by
    filter_upwards [halive] with z hz
    have : 0 < (fwdMap W s z).im := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hz
    exact this.le
  have h1 : Tendsto (fun z => F (fwdMap W s z)) (𝓝[H] (x : ℂ)) (𝓝 (F (fwdMap W s x))) :=
    (hFc _ hxHbar).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, hmaps⟩)
  have h2 : (fun z => F (fwdMap W s z)) =ᶠ[𝓝[H] (x : ℂ)] id := by
    filter_upwards [halive] with z hz
    rw [hFeq (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs hz), QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hs hz]
    rfl
  have h3 : Tendsto (id : ℂ → ℂ) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hne : (𝓝[H] (x : ℂ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
    exact mem_Hbar_of_im_eq_zero (by simp)
  exact tendsto_nhds_unique (h1.congr' h2) h3

/-! ### The real flow on half-lines -/

/-- The real flow at time `s` is continuous in the alive starting point. -/
theorem continuousWithinAt_fwdMap_real (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) {S : Set ℝ}
    (hS : ∀ x ∈ S, ∃ u, IsForwardSol W (x : ℂ) s u) {x₀ : ℝ} (hx₀ : x₀ ∈ S) :
    ContinuousWithinAt (fun x : ℝ => fwdMap W s x) S x₀ := by
  obtain ⟨u, hu⟩ := hS x₀ hx₀
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hs hu
  set E := Real.exp (2 / δ ^ 2 * s) with hE
  have hE0 : 0 < E := Real.exp_pos _
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min δ ε / (2 * E), by positivity, fun x hx hxd => ?_⟩
  obtain ⟨v, hv⟩ := hS x hx
  have hxx : ‖(x : ℂ) - x₀‖ * E < min δ ε / 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← Real.dist_eq]
    calc dist x x₀ * E < min δ ε / (2 * E) * E := mul_lt_mul_of_pos_right hxd hE0
      _ = min δ ε / 2 := by field_simp
  have hst := norm_sub_le_of_isForwardSol hW hu hv hδ hs le_rfl hlow
    (by linarith [min_le_left δ ε, hxx]) s ⟨hs, le_rfl⟩
  rw [dist_eq_norm, fwdMap_eq_of_isForwardSol hW hv ⟨hs, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hu ⟨hs, le_rfl⟩]
  calc ‖v s - u s‖ ≤ ‖(x : ℂ) - x₀‖ * Real.exp (2 / δ ^ 2 * s) := hst
    _ < min δ ε / 2 := hxx
    _ < ε := by linarith [min_le_right δ ε]

/-- **Intermediate values on the right**: for an alive mark `p > 0` and `ξ ≥ f_s(p)`, some alive `x ≥ p` has
`f_s(x) = ξ`. -/
theorem exists_fwdMap_real_eq_of_le (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {p : ℝ}
    (hp : 0 < p) {u : ℝ → ℂ} (hu : IsForwardSol W (p : ℂ) s u) {ξ : ℝ} (hξ : (fwdMap W s p).re ≤ ξ) :
    ∃ x : ℝ, p ≤ x ∧ (∃ v, IsForwardSol W (x : ℂ) s v) ∧ fwdMap W s x = ξ := by
  have halive : ∀ x ∈ Ici p, ∃ v, IsForwardSol W (x : ℂ) s v := fun x hx => by
    rcases (mem_Ici.1 hx).eq_or_lt with h | h
    · exact ⟨u, h ▸ hu⟩
    · exact QuantumZipper.RS.exists_isForwardSol_of_lt hW hs (by rw [hW0]; exact hp) h hu
  set g : ℝ → ℝ := fun x => (fwdMap W s x).re with hg
  have hgc : ContinuousOn g (Ici p) := fun x hx =>
    Complex.continuous_re.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_fwdMap_real hW hs halive hx)
  -- `g(x) ≥ x − W s`
  have hglow : ∀ x ∈ Ici p, x - W s ≤ g x := fun x hx => by
    obtain ⟨v, hv⟩ := halive x hx
    have hx0 : 0 < x := hp.trans_le hx
    have hmono := re_add_monotoneOn hW hW0 hx0 hs hv ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
    have h0 : (v 0).re + W 0 = x := by
      rw [(hv.2 0 ⟨le_rfl, hs⟩).2]; simp [hW0]
    simp only [hg, fwdMap_eq_of_isForwardSol hW hv ⟨hs, le_rfl⟩]
    linarith
  set b := max p (ξ + W s + 1) with hb
  have hpb : p ≤ b := le_max_left _ _
  have hgb : ξ ≤ g b := by
    have := hglow b (mem_Ici.2 hpb)
    have : ξ + W s + 1 ≤ b := le_max_right _ _
    linarith
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc hpb (hgc.mono Icc_subset_Ici_self) ⟨hξ, hgb⟩
  obtain ⟨v, hv⟩ := halive x (mem_Ici.2 hx.1)
  refine ⟨x, hx.1, ⟨v, hv⟩, Complex.ext ?_ ?_⟩
  · simpa [hg] using hgx
  · simp [im_fwdMap_real_eq_zero hW hv ⟨hs, le_rfl⟩]

/-- **Intermediate values on the left** (by reflection): for an alive mark `p < 0` and `ξ ≤ f_s(p)`, some alive
`x ≤ p` has `f_s(x) = ξ`. -/
theorem exists_fwdMap_real_eq_of_ge (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) {p : ℝ}
    (hp : p < 0) {u : ℝ → ℂ} (hu : IsForwardSol W (p : ℂ) s u) {ξ : ℝ} (hξ : ξ ≤ (fwdMap W s p).re) :
    ∃ x : ℝ, x ≤ p ∧ (∃ v, IsForwardSol W (x : ℂ) s v) ∧ fwdMap W s x = ξ := by
  have hW' : Continuous fun t => -W t := hW.neg
  have hW0' : (fun t => -W t) 0 = 0 := by simp [hW0]
  obtain ⟨u', hu'⟩ := (exists_isForwardSol_neg_iff (W := W) (x := p) (T := s)).2 ⟨u, hu⟩
  have hrefl := fwdMap_neg_real hW hu ⟨hs, le_rfl⟩
  have hξ' : (fwdMap (fun t => -W t) s ((-p : ℝ) : ℂ)).re ≤ -ξ := by
    rw [hrefl, Complex.neg_re]; linarith
  obtain ⟨x', hx', ⟨v', hv'⟩, hfx'⟩ := exists_fwdMap_real_eq_of_le hW' hW0' hs (by linarith) hu' hξ'
  have hv : ∃ v, IsForwardSol W ((-x' : ℝ) : ℂ) s v := by
    refine (exists_isForwardSol_neg_iff (W := W) (x := -x') (T := s)).1 ?_
    rw [neg_neg]; exact ⟨v', hv'⟩
  obtain ⟨v, hv⟩ := hv
  refine ⟨-x', by linarith, ⟨v, hv⟩, ?_⟩
  have h2 := fwdMap_neg_real hW hv ⟨hs, le_rfl⟩
  rw [neg_neg] at h2
  rw [hfx'] at h2
  push_cast at h2 ⊢
  linear_combination h2

end GB7a

end InteractingSLE
