import QuantumZipper.Proofs.GFF.K3.MixedLocal
import QuantumZipper.Proofs.GFF.K3.MixedRiesz
import QuantumZipper.Proofs.GFF.K3.GreenLower1
import QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov

/-!
# K3-mixed M7-a1, analytic part: a trace bound on the half-disc arc

Tools for `MixedPoissonBoundStmt` (the uniform bound `(∫ f dP_z)² ≤ C (f,f)_∇`):

* `mixed_local_L1_bound_m7a`: the `L¹` form `∫ |f| dμ ≤ M ‖∇f‖_{L²(D)}` of the local bound M4
  (`mixed_local_energy_bound`, whose proof in fact bounds `∫ |f| dμ`; the proof is copied from
  `MixedLocal.lean` with the last step changed);
* `ofReal_abs_le_ray_m7a`: along the ray from the centre `t`,
  `|f x| ≤ |f(t + ½(x−t))| + ∫_{r/2}^{r} ‖∇f(t + (ρ/r)(x−t))‖ dρ` for `‖x − t‖ ≤ r`;
* `foldH_circleMap_scale_m7a`: radial scaling about a real centre commutes with `foldH`;
* `lintegral_ray_foldedCircle_le_m7a`: the ray term averaged over the folded circle
  `foldedCircle t r` is bounded by `∫_D ‖∇f‖` (polar coordinates).

Own elementary argument (cost rule): the classical trace estimate by the fundamental theorem
of calculus along rays and averaging (cf. Gilbarg–Trudinger, *Elliptic PDE of Second Order*,
Lemma 7.16, p. 162, the same radial-integration device as M4). With the density bound
`P_z ≤ pBound r r' • foldedCircle t r` (`halfDiscPoisson_le`) this reduces the trace on the
semicircle to the local measure `foldedCircle t (r/2)`, uniformly in `z`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal

namespace QuantumZipper.K3

/-- **M4, `L¹` form** (proof copied from `mixed_local_energy_bound`). -/
theorem mixed_local_L1_bound_m7a {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {K : Set ℂ} {R : ℝ} (hR : 0 < R)
    (hKloc : ∀ z ∈ K, LocalBall D S z (2 * R)) {μ : Measure ℂ} (hμ : IsAdmissibleH μ)
    (hμK : μ Kᶜ = 0) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ f ∈ mixedSpace D S, ∫⁻ z, ENNReal.ofReal |f z| ∂μ ≤
      M * ENNReal.ofReal (Real.sqrt (∫ z in D, ‖fderiv ℝ f z‖ ^ 2)) := by
  obtain ⟨CP, hCP⟩ := mixed_poincare hD hDH hb hS
  have hμf := hμ.1
  have hKae : ∀ᵐ z ∂μ, z ∈ K := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμK] with z hz
    exact Set.notMem_compl_iff.mp hz
  set a : ℝ≥0∞ := ENNReal.ofReal (3 * R ^ 2 / 2) with ha
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * π)⁻¹ with hc
  set P : ℂ → ℝ≥0∞ := fun y => ∫⁻ z, kInv (2 * R) (y - z) ∂μ with hPdef
  have hPm : Measurable P :=
    Measurable.lintegral_prod_right' (ν := μ)
      ((measurable_kInv (2 * R)).comp (measurable_fst.sub measurable_snd))
  set PP : ℝ≥0∞ := ∫⁻ y, P y ^ (2 : ℝ) with hPP
  have hPP_lt : PP < ⊤ := lintegral_kInvPot_sq_lt_top hμ (by linarith)
  set VD : ℝ≥0∞ := volume D with hVD
  have hVD_lt : VD < ⊤ := hb.measure_lt_top
  set B : ℝ≥0∞ := c * 2 * μ univ * (VD ^ (1 / 2 : ℝ) * ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ)) +
    a * (c * 2 * PP ^ (1 / 2 : ℝ)) with hB
  have hB_ne : B ≠ ⊤ := by
    have h1 : VD ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hVD_lt.ne
    have h2 : ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    have h3 : PP ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hPP_lt.ne
    have h4 : μ univ ≠ ⊤ := measure_ne_top μ _
    have h5 : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h5) h4) (ENNReal.mul_ne_top h1 h2),
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h5) h3)⟩
  have ha0 : 0 < 3 * R ^ 2 / 2 := by positivity
  have ha_ne : a ≠ 0 := (ENNReal.ofReal_pos.2 ha0).ne'
  have ha_top : a ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨a⁻¹ * B, ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 ha_ne) hB_ne, fun f hf => ?_⟩
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le one_le_smooth
  have hfc : Continuous f := hf1.continuous
  have hdc : Continuous (fderiv ℝ f) := hf1.continuous_fderiv one_ne_zero
  set G : ℝ := ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 with hG
  have hG0 : 0 ≤ G := setIntegral_nonneg hD.measurableSet fun _ _ => sq_nonneg _
  have hGint : IntegrableOn (fun z => ‖fderiv ℝ f z‖ ^ 2) D := hf.2.1
  set Y : ℝ≥0∞ := ENNReal.ofReal G ^ (1 / 2 : ℝ) with hY
  -- (a) the energy as a lintegral
  have hEn : ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal G := by
    rw [hG, ofReal_integral_eq_lintegral_ofReal hGint
      (Eventually.of_forall fun _ => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
  -- (b) Poincaré
  have hfsq : IntegrableOn (fun z => f z ^ 2) D :=
    ((hfc.pow 2).continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have hL2 : ∫⁻ y in D, ‖f y‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (max CP 0) * ENNReal.ofReal G := by
    have e : ∫⁻ y in D, ‖f y‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∫ z in D, f z ^ 2) := by
      rw [ofReal_integral_eq_lintegral_ofReal hfsq (Eventually.of_forall fun _ => sq_nonneg _)]
      refine lintegral_congr fun y => ?_
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
        Real.rpow_two, sq_abs]
    rw [e, ← ENNReal.ofReal_mul (le_max_right _ _)]
    exact ENNReal.ofReal_le_ofReal
      ((hCP f hf).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hG0))
  -- (c) the `L¹` term
  set L1 := ∫⁻ y in D, ‖f y‖ₑ with hL1def
  have hL1 : L1 ≤ VD ^ (1 / 2 : ℝ) * (ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) * Y) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict D) Real.HolderConjugate.two_two
      (f := fun _ => (1 : ℝ≥0∞)) (g := fun y => ‖f y‖ₑ) aemeasurable_const
      hfc.enorm.measurable.aemeasurable
    simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const,
      Measure.restrict_apply_univ] at h
    refine h.trans (mul_le_mul_right ?_ _)
    calc (∫⁻ y in D, ‖f y‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (max CP 0) * ENNReal.ofReal G) ^ (1 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hL2 (by norm_num)
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  -- (d) the pointwise bound, integrated
  have hint1 : a * ∫⁻ z, ENNReal.ofReal |f z| ∂μ ≤ c * (2 * L1) * μ univ +
      a * (c * ∫⁻ z, (∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) ∂μ) := by
    rw [← lintegral_const_mul' a (fun z => ENNReal.ofReal |f z|) ENNReal.ofReal_ne_top]
    calc ∫⁻ z, a * ENNReal.ofReal |f z| ∂μ
        ≤ ∫⁻ z, (c * (2 * L1) +
          a * (c * ∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z)))) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hKae] with z hz
          exact local_pointwise_bound hD.measurableSet hf1 (hKloc z hz).1 hR
            (fun y hy hyz => (hKloc z hz).mem_of_mem_H hD hS hy hyz.le)
      _ = _ := by
          rw [lintegral_add_left measurable_const, lintegral_const,
            lintegral_const_mul' a _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' c _ ENNReal.ofReal_ne_top]
  -- (e) Tonelli, and restriction to `D`
  have hswap : ∫⁻ z, (∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) ∂μ ≤
      2 * ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ * P y := by
    have hm : Measurable fun p : ℂ × ℂ => ‖fderiv ℝ f p.2‖ₑ * (2 * kInv (2 * R) (p.2 - p.1)) :=
      (hdc.enorm.measurable.comp measurable_snd).mul
        (measurable_const.mul ((measurable_kInv _).comp (measurable_snd.sub measurable_fst)))
    have e : ∀ y, ∫⁻ z, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z)) ∂μ =
        2 * (‖fderiv ℝ f y‖ₑ * P y) := by
      intro y
      calc ∫⁻ z, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z)) ∂μ
          = ∫⁻ z, (‖fderiv ℝ f y‖ₑ * 2) * kInv (2 * R) (y - z) ∂μ := by simp_rw [mul_assoc]
        _ = (‖fderiv ℝ f y‖ₑ * 2) * P y :=
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top enorm_ne_top (by norm_num))
        _ = 2 * (‖fderiv ℝ f y‖ₑ * P y) := by ring
    rw [lintegral_lintegral_swap hm.aemeasurable, setLIntegral_congr_fun measurableSet_H_mx (fun y _ => e y),
      lintegral_const_mul' _ _ (by norm_num)]
    refine mul_le_mul_right ?_ 2
    rw [← lintegral_indicator measurableSet_H_mx, ← lintegral_indicator hD.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hyD : y ∈ D
    · rw [indicator_of_mem (hDH hyD), indicator_of_mem hyD]
    · rw [indicator_of_notMem hyD]
      by_cases hyH : y ∈ H
      · rw [indicator_of_mem hyH]
        have hP0 : P y = 0 := by
          rw [hPdef]
          refine (lintegral_congr_ae ?_).trans lintegral_zero
          filter_upwards [hKae] with z hz
          have hk : ¬ ‖y - z‖ < 2 * R := fun h =>
            hyD ((hKloc z hz).mem_of_mem_H hD hS hyH h.le)
          simp [kInv, hk]
        rw [hP0, mul_zero]
      · rw [indicator_of_notMem hyH]
  -- (f) Cauchy–Schwarz for the gradient term
  have hW : ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ * P y ≤ Y * PP ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict D) Real.HolderConjugate.two_two
      (f := fun y => ‖fderiv ℝ f y‖ₑ) (g := P) hdc.enorm.measurable.aemeasurable hPm.aemeasurable
    simp only [Pi.mul_apply] at h
    refine h.trans (mul_le_mul' (le_of_eq ?_)
      (ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by norm_num)))
    rw [hEn]
  -- (g) combination
  have hmain : a * ∫⁻ z, ENNReal.ofReal |f z| ∂μ ≤ Y * B := by
    calc a * ∫⁻ z, ENNReal.ofReal |f z| ∂μ
        ≤ c * (2 * L1) * μ univ +
          a * (c * ∫⁻ z, (∫⁻ y in H, ‖fderiv ℝ f y‖ₑ * (2 * kInv (2 * R) (y - z))) ∂μ) := hint1
      _ ≤ c * (2 * (VD ^ (1 / 2 : ℝ) * (ENNReal.ofReal (max CP 0) ^ (1 / 2 : ℝ) * Y))) * μ univ +
          a * (c * (2 * (Y * PP ^ (1 / 2 : ℝ)))) := by
          refine add_le_add (mul_le_mul_left (mul_le_mul_right (mul_le_mul_right hL1 2) c) _)
            (mul_le_mul_right (mul_le_mul_right (hswap.trans (mul_le_mul_right hW 2)) c) a)
      _ = Y * B := by rw [hB]; ring
  have hYeq : Y = ENNReal.ofReal (Real.sqrt G) := by
    rw [hY, Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg hG0 (by norm_num)]
  rw [← hYeq]
  calc ∫⁻ z, ENNReal.ofReal |f z| ∂μ = a⁻¹ * (a * ∫⁻ z, ENNReal.ofReal |f z| ∂μ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha_ne ha_top, one_mul]
    _ ≤ a⁻¹ * (Y * B) := mul_le_mul_right hmain _
    _ = a⁻¹ * B * Y := by ring

/-! ## The ray bound -/

/-- **Ray bound.** For `‖x − t‖ ≤ r`, the fundamental theorem of calculus along
`ρ ↦ t + (ρ/r)(x − t)`, `ρ ∈ [r/2, r]`. -/
theorem ofReal_abs_le_ray_m7a {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (t : ℂ) {r : ℝ} (hr : 0 < r)
    {x : ℂ} (hx : ‖x - t‖ ≤ r) :
    ENNReal.ofReal |f x| ≤ ENNReal.ofReal |f (t + (((r / 2) / r : ℝ) : ℂ) * (x - t))| +
      ∫⁻ ρ in Ioc (r / 2) r, ‖fderiv ℝ f (t + ((ρ / r : ℝ) : ℂ) * (x - t))‖ₑ := by
  set γ : ℝ → ℂ := fun ρ => t + ((ρ / r : ℝ) : ℂ) * (x - t) with hγdef
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have hγc : Continuous γ := by rw [hγdef]; fun_prop
  have hγ : ∀ ρ, HasDerivAt γ (((1 / r : ℝ) : ℂ) * (x - t)) ρ := by
    intro ρ
    have h1 : HasDerivAt (fun ρ : ℝ => ((ρ / r : ℝ) : ℂ)) ((1 / r : ℝ) : ℂ) ρ :=
      ((hasDerivAt_id ρ).div_const r).ofReal_comp
    exact (h1.mul_const (x - t)).const_add t
  have hd : ∀ ρ, HasDerivAt (fun ρ => f (γ ρ))
      (fderiv ℝ f (γ ρ) (((1 / r : ℝ) : ℂ) * (x - t))) ρ :=
    fun ρ => ((hf.differentiable one_ne_zero (γ ρ)).hasFDerivAt).comp_hasDerivAt ρ (hγ ρ)
  have hdcont : Continuous fun ρ => fderiv ℝ f (γ ρ) (((1 / r : ℝ) : ℂ) * (x - t)) :=
    (hdc.comp hγc).clm_apply continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun ρ _ => hd ρ)
    (hdcont.intervalIntegrable (r / 2) r)
  have hγr : γ r = x := by
    show t + ((r / r : ℝ) : ℂ) * (x - t) = x
    rw [div_self hr.ne', Complex.ofReal_one, one_mul, add_sub_cancel]
  have hnorm : ∀ ρ, ‖fderiv ℝ f (γ ρ) (((1 / r : ℝ) : ℂ) * (x - t))‖ ≤ ‖fderiv ℝ f (γ ρ)‖ := by
    intro ρ
    have h1 : ‖((1 / r : ℝ) : ℂ) * (x - t)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), one_div,
        inv_mul_le_iff₀ hr]
      linarith
    calc _ ≤ ‖fderiv ℝ f (γ ρ)‖ * ‖((1 / r : ℝ) : ℂ) * (x - t)‖ := (fderiv ℝ f (γ ρ)).le_opNorm _
      _ ≤ ‖fderiv ℝ f (γ ρ)‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = _ := mul_one _
  have hgi : IntegrableOn (fun ρ => ‖fderiv ℝ f (γ ρ)‖) (Ioc (r / 2) r) :=
    ((hdc.comp hγc).norm.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hreal : |f x| ≤ |f (γ (r / 2))| + ∫ ρ in Ioc (r / 2) r, ‖fderiv ℝ f (γ ρ)‖ := by
    have e : f x = f (γ (r / 2)) +
        ∫ ρ in (r / 2)..r, fderiv ℝ f (γ ρ) (((1 / r : ℝ) : ℂ) * (x - t)) := by
      rw [hFTC, hγr]; ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    gcongr
    rw [intervalIntegral.integral_of_le (by linarith), ← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le hgi (Eventually.of_forall hnorm)
  calc ENNReal.ofReal |f x|
      ≤ ENNReal.ofReal (|f (γ (r / 2))| + ∫ ρ in Ioc (r / 2) r, ‖fderiv ℝ f (γ ρ)‖) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal |f (γ (r / 2))| + ∫⁻ ρ in Ioc (r / 2) r, ‖fderiv ℝ f (γ ρ)‖ₑ := by
        rw [ENNReal.ofReal_add (abs_nonneg _)
            (setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _),
          ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun _ => norm_nonneg _)]
        simp only [ofReal_norm]

/-! ## Radial scaling of folded circles about a real centre -/

theorem foldH_circleMap_scale_m7a (t : ℝ) {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ) (θ : ℝ) :
    (t : ℂ) + ((ρ / r : ℝ) : ℂ) * (foldH (circleMap (t : ℂ) r θ) - t) =
      foldH (circleMap (t : ℂ) ρ θ) := by
  have him : ∀ s : ℝ, (circleMap (t : ℂ) s θ).im = s * Real.sin θ := by
    intro s
    simp only [circleMap, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, zero_add, zero_mul, add_zero]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  unfold foldH
  rw [him, him]
  split_ifs with h1 h2 h2
  · simp only [circleMap, Complex.ofReal_div]
    field_simp
    ring
  · exact absurd (mul_nonneg hρ.le (nonneg_of_mul_nonneg_right h1 hr)) h2
  · exact absurd (mul_nonneg hr.le (nonneg_of_mul_nonneg_right h2 hρ)) h1
  · simp only [circleMap, map_add, map_mul, Complex.conj_ofReal, Complex.ofReal_div]
    field_simp
    ring

/-! ## The ray term averaged over the folded circle -/

theorem lintegral_ray_foldedCircle_le_m7a {D : Set ℂ} (hDm : MeasurableSet D) {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) (t : ℝ) {r : ℝ} (hr : 0 < r)
    (hsub : ∀ y ∈ H, ‖y - t‖ < r → y ∈ D) :
    ∫⁻ x, (∫⁻ ρ in Ioc (r / 2) r, ‖fderiv ℝ f ((t : ℂ) + ((ρ / r : ℝ) : ℂ) * (x - t))‖ₑ)
        ∂(foldedCircle (t : ℂ) r) ≤
      (ENNReal.ofReal (2 * π))⁻¹ * ENNReal.ofReal (2 / r) *
        (2 * ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ) := by
  have hdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  set g : ℂ → ℝ≥0∞ := fun y => ‖fderiv ℝ f (foldH y)‖ₑ with hg
  have hgm : Measurable g := (hdc.comp continuous_foldH_K3).enorm.measurable
  have hFm : Measurable fun x : ℂ => ∫⁻ ρ in Ioc (r / 2) r,
      ‖fderiv ℝ f ((t : ℂ) + ((ρ / r : ℝ) : ℂ) * (x - t))‖ₑ :=
    Measurable.lintegral_prod_right'
      (f := fun p : ℂ × ℝ => ‖fderiv ℝ f ((t : ℂ) + ((p.2 / r : ℝ) : ℂ) * (p.1 - t))‖ₑ)
      (hdc.comp (by fun_prop)).enorm.measurable
  have hFm' : Measurable fun a : ℂ => ∫⁻ ρ in Ioc (r / 2) r,
      ‖fderiv ℝ f ((t : ℂ) + ((ρ / r : ℝ) : ℂ) * (foldH a - t))‖ₑ :=
    hFm.comp measurable_foldH
  rw [foldedCircle, lintegral_map hFm measurable_foldH, lintegral_circleUnif_eq' hFm', mul_assoc]
  refine mul_le_mul_right ?_ _
  have hinner : ∀ θ, ∫⁻ ρ in Ioc (r / 2) r,
      ‖fderiv ℝ f ((t : ℂ) + ((ρ / r : ℝ) : ℂ) * (foldH (circleMap (t : ℂ) r θ) - t))‖ₑ =
      ∫⁻ ρ in Ioc (r / 2) r, g (circleMap (t : ℂ) ρ θ) := by
    intro θ
    refine setLIntegral_congr_fun measurableSet_Ioc (fun ρ hρ => ?_)
    rw [foldH_circleMap_scale_m7a t hr (by linarith [hρ.1]) θ]
  have hsw : Measurable (Function.uncurry fun θ ρ => g (circleMap (t : ℂ) ρ θ)) :=
    hgm.comp ((continuous_circleMap_uncurry (t : ℂ)).comp continuous_swap).measurable
  rw [lintegral_congr (fun θ => hinner θ), lintegral_lintegral_swap hsw.aemeasurable]
  calc ∫⁻ ρ in Ioc (r / 2) r, ∫⁻ θ in Ioo (-π) π, g (circleMap (t : ℂ) ρ θ)
      ≤ ∫⁻ ρ in Ioc (r / 2) r, ENNReal.ofReal (2 / r) *
          ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * g (circleMap (t : ℂ) ρ θ) := by
        refine setLIntegral_mono' measurableSet_Ioc (fun ρ hρ => ?_)
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_mono fun θ => ?_
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        have h1 : 1 ≤ 2 / r * ρ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hr]; linarith [hρ.1]
        calc g (circleMap (t : ℂ) ρ θ) = 1 * g (circleMap (t : ℂ) ρ θ) := (one_mul _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_right (ENNReal.one_le_ofReal.2 h1) zero_le
    _ = ENNReal.ofReal (2 / r) * ∫⁻ ρ in Ioc (r / 2) r,
          ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal ρ * g (circleMap (t : ℂ) ρ θ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 / r) * (2 * ∫⁻ y in D, ‖fderiv ℝ f y‖ₑ) := by
        refine mul_le_mul_right ?_ _
        rw [setLIntegral_congr Ioo_ae_eq_Ioc.symm]
        exact (lintegral_radius_circle_le hgm (t : ℂ) (by linarith : (0 : ℝ) ≤ r / 2)).trans
          (lintegral_ball_foldH_le hDm (show (t : ℂ) ∈ Hbar by simp [Hbar]) hsub
            hdc.enorm.measurable)

end QuantumZipper.K3
