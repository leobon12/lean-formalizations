import QuantumZipper.Proofs.Thm11.NonSwallowing

/-!
# DF-1 and DF-3: the clock tail bound and clock integrability, `κ ∈ (0,4]`

Blueprint `THM11_BLUEPRINT.md` §5. The clock `S_T(a) = fwdClock W T a = ∫₀ᵀ |f_s(a)|⁻² ds`.
In the setting of `NonSwallowing.lean` (tamed motion `U`, exit time `τ` of the annular region
`{ρ < |z| < R, Im z > c}`, capped at `T`) we apply the stopped Dynkin identity to a smooth cutoff
of a *clock function* `Φ` with `LΦ = λ/|z|²` on the region:

* `κ < 4`: `Φ = V = −log|z| + ((4−κ)/4) g(arg z)` (`ε = 0`), `λ = −(4−κ)/2`;
* `κ = 4`: `Φ = |log z|² = log²|z| + arg² z`, `λ = 4`.

This gives `E[∫₀^τ |U|⁻²] ≤ sup_region (Φ − Φ(a))/λ` (DF-1(iii), and DF-3 for `κ < 4`), hence
`P(S_T(a) > u) ≤ P(exit before T) + sup_region ((Φ − Φ(a))/λ)/u`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

noncomputable section

namespace QuantumZipper
namespace NonSwallow

open FwdClock Thm11Lyap FwdHolo

/-! ### A generic smooth cutoff -/

/-- A `C³` function with bounded derivatives (up to order 3) agreeing near
`{ρ ≤ |z| ≤ R, Im z ≥ c}` with a function `Φ` that is `C³` on `ℍ`. -/
theorem exists_cutoff_of_contDiffAt (Φ : ℂ → ℝ) (hΦ : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 3 Φ z)
    {ρ R c : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (hc : 0 < c) :
    ∃ F : ℂ → ℝ, ∃ C : ℝ, ContDiff ℝ 3 F ∧
      (∀ x, |F x| ≤ C ∧ ‖fderiv ℝ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 3 F x‖ ≤ C) ∧
      ∀ z ∈ annReg ρ R c, F =ᶠ[𝓝 z] Φ := by
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      (isOpen_annOpen (ρ / 4) (4 * R) (c / 4)) (isClosed_annReg (ρ / 2) (2 * R) (c / 2))
      (annReg_subset_annOpen (by linarith) (by linarith) (by linarith))
  have hts : tsupport χ ⊆ annReg (ρ / 4) (4 * R) (c / 4) := by
    rw [tsupport, hχs]; exact closure_minimal annOpen_subset_annReg (isClosed_annReg _ _ _)
  have hχc : HasCompactSupport χ :=
    (isCompact_annReg _ _ _).of_isClosed_subset (isClosed_tsupport χ) hts
  set F : ℂ → ℝ := χ * Φ with hFdef
  have hFs : ContDiff ℝ 3 F := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : 0 < x.im
    · exact (hχ.contDiffAt.of_le three_le_smooth).mul (hΦ x hx)
    · have hxt : x ∉ tsupport χ := fun h => hx (by have := (hts h).2.2; linarith)
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hxt
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (h0.mono fun y hy => by simp [hFdef, hy])
  have hFc : HasCompactSupport F := hχc.mul_right
  obtain ⟨C0, h0⟩ := hFs.continuous.bounded_above_of_compact_support hFc
  obtain ⟨C1, h1⟩ := (hFs.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hFc.fderiv (𝕜 := ℝ))
  obtain ⟨C2, h2⟩ := (hFs.continuous_iteratedFDeriv (m := 2) (by norm_num)).bounded_above_of_compact_support
    (hFc.iteratedFDeriv 2)
  obtain ⟨C3, h3⟩ := (hFs.continuous_iteratedFDeriv (m := 3) le_rfl).bounded_above_of_compact_support
    (hFc.iteratedFDeriv 3)
  refine ⟨F, max (max C0 C1) (max C2 C3), hFs, fun x => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← Real.norm_eq_abs]
    exact (h0 x).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (h1 x).trans ((le_max_right _ _).trans (le_max_left _ _))
  · exact (h2 x).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h3 x).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro z hz
    have hmem : annOpen (ρ / 2) (2 * R) (c / 2) ∈ 𝓝 z :=
      (isOpen_annOpen _ _ _).mem_nhds
        (annReg_subset_annOpen (by linarith) (by linarith) (by linarith) hz)
    filter_upwards [hmem] with y hy
    have : χ y = 1 := (hχ1 y).1 (annOpen_subset_annReg hy)
    simp [hFdef, this]

/-! ### The clock function for `κ = 4` -/

/-- `|log z|² = log²|z| + arg² z`. -/
def logSq (z : ℂ) : ℝ :=
  (Complex.log z).re * (Complex.log z).re + (Complex.log z).im * (Complex.log z).im

theorem contDiffAt_logSq {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) logSq z := by
  have hlog : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Complex.log z :=
    (Complex.contDiffAt_log (mem_slitPlane_of_im_pos hz)).restrict_scalars ℝ
  have hre : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (Complex.log z).re) z :=
    Complex.reCLM.contDiff.contDiffAt.comp z hlog
  have him : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (Complex.log z).im) z :=
    Complex.imCLM.contDiff.contDiffAt.comp z hlog
  exact (hre.mul hre).add (him.mul him)

theorem fderiv_logSq_apply {z : ℂ} (hz : 0 < z.im) (w : ℂ) :
    fderiv ℝ logSq z w = 2 * (Complex.log z).re * (w * z⁻¹).re
      + 2 * (Complex.log z).im * (w * z⁻¹).im := by
  have hlog := hasFDerivAt_log_real hz
  have h1 := Complex.reCLM.hasFDerivAt.comp z hlog
  have h2 := Complex.imCLM.hasFDerivAt.comp z hlog
  have h : HasFDerivAt logSq _ z := (h1.mul h1).add (h2.mul h2)
  rw [h.fderiv]
  simp [smul_eq_mul]
  ring

/-- **`L(|log z|²) = 4/|z|²` at `κ = 4`**, where the taming is inactive. -/
theorem dynkinGen_logSq_four {c : ℝ} {z : ℂ} (hz : c ≤ z.im) (hz0 : 0 < z.im) :
    dynkinGen (tamedZField c) (-((Real.sqrt 4 : ℝ) : ℂ)) logSq z = 4 / ‖z‖ ^ 2 := by
  have hzne : z ≠ 0 := fun h => by simp [h] at hz0
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  set e : ℂ := -((Real.sqrt 4 : ℝ) : ℂ) with he
  set q : ℝ → ℂ := fun s => z + (s : ℂ) * e with hqdef
  have hq : HasDerivAt q e 0 := by
    simpa [hqdef] using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const e).const_add z
  have hq0 : q 0 = z := by simp [hqdef]
  have hinv : HasDerivAt (fun s => (q s)⁻¹) (-(z ^ 2)⁻¹ * e) 0 :=
    (hasDerivAt_inv hzne).comp_of_eq 0 hq hq0.symm
  have hA : HasDerivAt (fun s => e * (q s)⁻¹) (e * (-(z ^ 2)⁻¹ * e)) 0 := hinv.const_mul e
  have hAre : HasDerivAt (fun s => (e * (q s)⁻¹).re) (e * (-(z ^ 2)⁻¹ * e)).re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 hA rfl
  have hAim : HasDerivAt (fun s => (e * (q s)⁻¹).im) (e * (-(z ^ 2)⁻¹ * e)).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 hA rfl
  have hlogq : HasDerivAt (fun s => Complex.log (q s)) (e / q 0) 0 :=
    hq.clog_real (by rw [hq0]; exact mem_slitPlane_of_im_pos hz0)
  have hlogre : HasDerivAt (fun s => (Complex.log (q s)).re) (e / q 0).re 0 :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 hlogq rfl
  have hlogim : HasDerivAt (fun s => (Complex.log (q s)).im) (e / q 0).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt_of_eq 0 hlogq rfl
  have hφ := ((hlogre.const_mul 2).mul hAre).add ((hlogim.const_mul 2).mul hAim)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), fderiv ℝ logSq (z + ((s : ℝ) : ℂ) * e) e =
      (fun s => 2 * (Complex.log (q s)).re * (e * (q s)⁻¹).re
        + 2 * (Complex.log (q s)).im * (e * (q s)⁻¹).im) s := by
    have hmem : {w : ℂ | 0 < w.im} ∈ 𝓝 (q 0) := isOpen_upper.mem_nhds (by rw [hq0]; exact hz0)
    filter_upwards [hq.continuousAt.preimage_mem_nhds hmem] with s hs
    exact fderiv_logSq_apply hs e
  have hC2 : ContDiffAt ℝ 2 logSq z := (contDiffAt_logSq hz0).of_le (by
    exact WithTop.coe_le_coe.2 le_top)
  unfold dynkinGen
  rw [tamedZField_of_le hz, fderiv_logSq_apply hz0,
    iteratedFDeriv_two_eq_of_line hC2 e hev hφ]
  have hn2 : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  rw [hn2]
  simp only [hq0, he, hs4, pow_two, mul_inv, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.inv_re, Complex.inv_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply, Complex.re_ofNat,
    Complex.im_ofNat]
  have hr0 : z.re * z.re + z.im * z.im ≠ 0 := by
    have : 0 < z.im * z.im := mul_pos hz0 hz0
    nlinarith [mul_self_nonneg z.re]
  field_simp
  ring

theorem abs_logSq_le {z : ℂ} : |logSq z| ≤ Real.log ‖z‖ ^ 2 + Real.pi ^ 2 := by
  have e : logSq z = Real.log ‖z‖ ^ 2 + Complex.arg z ^ 2 := by
    rw [logSq, Complex.log_re, Complex.log_im]; ring
  have h1 : Complex.arg z ^ 2 ≤ Real.pi ^ 2 := by
    rw [sq_le_sq, abs_of_pos Real.pi_pos]; exact Complex.abs_arg_le_pi z
  rw [e, abs_of_nonneg (by positivity)]
  linarith

/-! ### The clock estimate -/

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **DF-1(iii)/DF-3, clock estimate.** If `Φ` is `C³` on `ℍ`, `LΦ = λ/|z|²` on the closed
region and `|Φ| ≤ M_Φ` there, then the probability that the tamed motion stays in the open
region up to `T` while its clock exceeds `u` is at most `2M_Φ/(|λ| u)`. -/
theorem prob_clock_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} {a : ℂ} {ρ R c : ℝ} (T : ℝ≥0)
    (hρ : 0 < ρ) (hR : 0 < R) (hc : 0 < c) (ha : a ∈ annOpen ρ R c)
    (Φ : ℂ → ℝ) (hΦ : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 3 Φ z) {lam M : ℝ} (hlam : lam ≠ 0)
    (hgen : ∀ z ∈ annReg ρ R c,
      dynkinGen (tamedZField c) (-((Real.sqrt κ : ℝ) : ℂ)) Φ z = lam / ‖z‖ ^ 2)
    (hbound : ∀ z ∈ annReg ρ R c, (Φ z - Φ a) / lam ≤ M) {u : ℝ} (hu : 0 < u) :
    (∫⁻ ω, {ω | B 0 ω = 0 ∧ ∀ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c}.indicator
        (fun ω => ENNReal.ofReal (∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2)) ω ∂P
      ≤ ENNReal.ofReal M) ∧
    P {ω | B 0 ω = 0 ∧ (∀ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c) ∧
      u < ∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2}
      ≤ ENNReal.ofReal (M / u) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set e : ℂ := -((Real.sqrt κ : ℝ) : ℂ) with he
  set 𝓕 := bmFilt hBm with h𝓕
  set U : ℝ≥0 → Ω → ℂ := fun t ω => tamedZ (drive κ B ω) c a t with hUdef
  have hU : ∀ ω (t : ℝ≥0),
      U t ω = a + (∫ r in (0 : ℝ)..t, tamedZField c (U r.toNNReal ω)) + B t ω • e :=
    fun ω t => tamedZ_integralEq hBc hc κ a ω t
  have hbM : ∀ x, ‖tamedZField c x‖ ≤ 2 / c := norm_tamedZField_le hc
  have hb := lipschitz_tamedZField hc
  have hUc : ∀ ω, Continuous (U · ω) :=
    Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  have hUm : ∀ t, Measurable[𝓕 t] (U t) :=
    Dynkin.measurable_of_integralEq 𝓕 (bmFilt_adapted hBm) hBc hb hbM hU hUc
  obtain ⟨F, C, hF, hFC, hFV⟩ := exists_cutoff_of_contDiffAt Φ hΦ hρ hR hc
  set E := exitSet ρ R c with hE
  set τ : Ω → ℝ≥0 := hittingBtwn U E 0 T with hτdef
  have hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUm hUc (isClosed_exitSet ρ R c) T
  have hτT : ∀ ω, τ ω ≤ T := fun ω => hittingBtwn_le ω
  have hB0 := hB.eval_zero_ae_eq_zero
  have hU0' : ∀ ω, B 0 ω = 0 → U 0 ω = a := by
    intro ω hω; rw [hU ω 0]; simp [hω]
  have hU0 : ∀ᵐ ω ∂P, U 0 ω = a := by
    filter_upwards [hB0] with ω hω using hU0' ω hω
  obtain ⟨hint, hzero⟩ := dynkin_stopped hB hBc 𝓕 (bmFilt_adapted hBm) (bmFilt_le_past hBm)
    hb hbM hU hF (fun x => (hFC x).2) (fun x => (hFC x).1) hU0 hτ T hτT
  have hK : ∀ ω, B 0 ω = 0 → ∀ t ≤ τ ω, U t ω ∈ annReg ρ R c := by
    intro ω hω
    refine mem_of_le_of_forall_lt (isClosed_annReg ρ R c) (hUc ω) ?_ ?_
    · rw [hU0' ω hω]; exact annOpen_subset_annReg ha
    · intro t ht
      exact annOpen_subset_annReg
        (notMem_exitSet_iff.1 (notMem_of_lt_hittingBtwn ht zero_le))
  have hτm : Measurable τ := by
    refine measurable_of_Iic fun x => ?_
    have h := 𝓕.le x _ (hτ x)
    have e : τ ⁻¹' Iic x = {ω | ((τ ω : ℝ≥0) : WithTop ℝ≥0) ≤ (x : WithTop ℝ≥0)} := by
      ext ω; simp only [mem_preimage, mem_Iic]; exact WithTop.coe_le_coe.symm
    rw [e]; exact h
  have hUj : Measurable (Function.uncurry U) :=
    measurable_uncurry_of_continuous_of_measurable hUc fun t => (hUm t).mono (𝓕.le t) le_rfl
  have hFUm : Measurable fun ω => F (U (τ ω) ω) :=
    hF.continuous.measurable.comp (hUj.comp (hτm.prodMk measurable_id))
  have hFUi : Integrable (fun ω => F (U (τ ω) ω)) P :=
    ItoLite.integrable_of_bound_abs hFUm.stronglyMeasurable fun ω => (hFC _).1
  -- the clock along the stopped path
  set J : Ω → ℝ := fun ω => ∫ r in (0 : ℝ)..(τ ω), 1 / ‖U r.toNNReal ω‖ ^ 2 with hJdef
  set Mf : Ω → ℝ := fun ω => F (U (τ ω) ω) - F a
    - ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F (U r.toNNReal ω) with hMf
  have hGJ : ∀ ω, B 0 ω = 0 →
      ∫ r in (0 : ℝ)..(τ ω), dynkinGen (tamedZField c) e F (U r.toNNReal ω) = lam * J ω := by
    intro ω hω
    simp only [hJdef]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (NNReal.coe_nonneg _)] at hr
    have hle : r.toNNReal ≤ τ ω := Real.toNNReal_le_iff_le_coe.2 hr.2
    have hmem := hK ω hω _ hle
    simp only
    rw [dynkinGen_congr (hFV _ hmem), hgen _ hmem]
    ring
  have hJeq : J =ᵐ[P] fun ω => (F (U (τ ω) ω) - F a - Mf ω) / lam := by
    filter_upwards [hB0] with ω hω
    rw [eq_div_iff hlam]
    have := hGJ ω hω
    simp only [hMf]
    linarith
  have hJi : Integrable J P :=
    (((hFUi.sub (integrable_const _)).sub hint).div_const lam).congr hJeq.symm
  have hJnn : ∀ ω, 0 ≤ J ω := fun ω =>
    intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) (fun r _ => by positivity)
  have hJT : ∀ ω, (∀ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c) →
      J ω = ∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2 := by
    intro ω hin
    have hno : ¬ ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ E := by
      rintro ⟨j, hj, hjE⟩
      exact (notMem_exitSet_iff.2 (hin j ⟨j.coe_nonneg, by exact_mod_cast hj.2⟩)) hjE
    have hτeq : τ ω = T := by
      show hittingBtwn U E 0 T ω = T
      rw [hittingBtwn_def]
      exact if_neg hno
    show ∫ r in (0 : ℝ)..(τ ω), 1 / ‖U r.toNNReal ω‖ ^ 2 = _
    rw [hτeq]
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le T.coe_nonneg] at hr
    simp only [hUdef, Real.coe_toNNReal r hr.1]
  have hEJ : ∫ ω, J ω ∂P ≤ M := by
    have i1 : Integrable (fun ω => F (U (τ ω) ω) - F a) P := hFUi.sub (integrable_const _)
    have h1 : ∫ ω, J ω ∂P = ∫ ω, (F (U (τ ω) ω) - F a) / lam ∂P := by
      rw [integral_congr_ae hJeq, integral_div, integral_sub i1 hint, hzero, sub_zero,
        integral_div]
    rw [h1]
    have hb' : ∀ᵐ ω ∂P, (F (U (τ ω) ω) - F a) / lam ≤ M := by
      filter_upwards [hB0] with ω hω
      have hmem := hK ω hω _ le_rfl
      rw [(hFV _ hmem).eq_of_nhds, (hFV a (annOpen_subset_annReg ha)).eq_of_nhds]
      exact hbound _ hmem
    calc ∫ ω, (F (U (τ ω) ω) - F a) / lam ∂P ≤ ∫ _ω, M ∂P :=
          integral_mono_ae (i1.div_const lam) (integrable_const _) hb'
      _ = M := by simp
  refine ⟨?_, ?_⟩
  · calc ∫⁻ ω, {ω | B 0 ω = 0 ∧ ∀ s ∈ Icc (0 : ℝ) T,
            tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c}.indicator
          (fun ω => ENNReal.ofReal (∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2)) ω ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (J ω) ∂P := by
          apply lintegral_mono
          intro ω
          by_cases hω : ω ∈ {ω | B 0 ω = 0 ∧ ∀ s ∈ Icc (0 : ℝ) T,
              tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c}
          · rw [Set.indicator_of_mem hω]; show _ ≤ ENNReal.ofReal (J ω); rw [hJT ω hω.2]
          · rw [Set.indicator_of_notMem hω]; exact zero_le
      _ = ENNReal.ofReal (∫ ω, J ω ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hJi (ae_of_all _ hJnn)).symm
      _ ≤ ENNReal.ofReal M := ENNReal.ofReal_le_ofReal hEJ
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hJnn) hJi u
  have hsub : {ω | B 0 ω = 0 ∧ (∀ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c) ∧
      u < ∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2} ⊆ {ω | u ≤ J ω} := by
    rintro ω ⟨-, hin, hlt⟩
    show u ≤ J ω
    rw [hJT ω hin]; exact hlt.le
  calc P {ω | B 0 ω = 0 ∧ (∀ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c) ∧
        u < ∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2}
      ≤ P {ω | u ≤ J ω} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | u ≤ J ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (M / u) := by
        apply ENNReal.ofReal_le_ofReal
        rw [le_div_iff₀ hu]
        linarith

/-- **DF-1, clock tail (two-parameter form).** For `κ ∈ (0,4]`,
`P(S_T(a) > u) ≤ P(exit) + 2M_Φ/(|λ|u)` with the exit bound of `prob_exit_le`. -/
theorem prob_clock_gt_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    {a : ℂ} {ρ R c ε : ℝ} (T : ℝ≥0) (hρ : 0 < ρ) (hρR : ρ < R) (hc : 0 < c) (hε : 0 < ε)
    (ha : a ∈ annOpen ρ R c) (hcsmall : c < a.im * Real.exp (-2 * ((T : ℝ) / ρ ^ 2)))
    (Φ : ℂ → ℝ) (hΦ : ∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 3 Φ z) {lam M : ℝ} (hlam : lam ≠ 0)
    (hgen : ∀ z ∈ annReg ρ R c,
      dynkinGen (tamedZField c) (-((Real.sqrt κ : ℝ) : ℂ)) Φ z = lam / ‖z‖ ^ 2)
    (hbound : ∀ z ∈ annReg ρ R c, (Φ z - Φ a) / lam ≤ M) {u : ℝ} (hu : 0 < u) :
    P {ω | u < fwdClock (drive κ B ω) T a} ≤ ENNReal.ofReal
      ((lyapV κ ε a + T * (ε * (κ + 4)) + Real.log R + (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ))
        / min (Real.log R - Real.log ρ) (ε * R ^ 2))
      + ENNReal.ofReal (M / u) := by
  have hR : 0 < R := hρ.trans hρR
  have ha0 : 0 < a.im := hc.trans ha.2.2
  have hnull : P {ω | ¬ B 0 ω = 0} = 0 := ae_iff.1 hB.eval_zero_ae_eq_zero
  have hsub : {ω | u < fwdClock (drive κ B ω) T a} ⊆
      ({ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c}
        ∪ {ω | B 0 ω = 0 ∧ (∀ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c) ∧
          u < ∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2})
        ∪ {ω | ¬ B 0 ω = 0} := by
    intro ω hω
    by_cases h0 : B 0 ω = 0
    swap
    · exact Or.inr h0
    left
    by_cases hex : ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c
    · exact Or.inl ⟨h0, hex⟩
    · push Not at hex
      refine Or.inr ⟨h0, hex, ?_⟩
      have hW := continuous_drive_ns hBc κ ω
      obtain ⟨-, heq⟩ := fwdMap_eq_tamedZ hW hc T.coe_nonneg ha0
        (fun s hs => (hex s hs).2.2.le)
      have : fwdClock (drive κ B ω) T a
          = ∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2 := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le T.coe_nonneg] at hs
        simp only [heq s hs]
      rw [← this]; exact hω
  calc P {ω | u < fwdClock (drive κ B ω) T a}
      ≤ P (({ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c}
        ∪ {ω | B 0 ω = 0 ∧ (∀ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c) ∧
          u < ∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2})
        ∪ {ω | ¬ B 0 ω = 0}) := measure_mono hsub
    _ ≤ P {ω | B 0 ω = 0 ∧ ∃ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∉ annOpen ρ R c}
        + P {ω | B 0 ω = 0 ∧ (∀ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c) ∧
          u < ∫ s in (0 : ℝ)..T, 1 / ‖tamedZ (drive κ B ω) c a s‖ ^ 2}
        + P {ω | ¬ B 0 ω = 0} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := by
        rw [hnull, add_zero]
        exact add_le_add (prob_exit_le hB hBm hBc hκ hκ4 T hρ hρR hc hε ha hcsmall)
          (prob_clock_le hB hBm hBc T hρ hR hc ha Φ hΦ hlam hgen hbound hu).2

/-! ### The clock functions -/

theorem abs_log_norm_le_of_mem_annReg {ρ R c : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : z ∈ annReg ρ R c) :
    |Real.log ‖z‖| ≤ max |Real.log ρ| |Real.log R| :=
  abs_le_max_abs_abs (Real.log_le_log hρ hz.1) (Real.log_le_log (hρ.trans_le hz.1) hz.2.1)

/-- Clock function data for `κ < 4`: `Φ = V` with `ε = 0`, `λ = −(4−κ)/2`, and the one-sided
bound `(Φ(z) − Φ(a))/λ ≤ 2(V(a) + log R + C_g)/(4−κ)` on the region. -/
theorem clock_data_lt_four {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {ρ R c : ℝ} (hρ : 0 < ρ)
    (hc : 0 < c) (a : ℂ) :
    (∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 3 (lyapV κ 0) z) ∧ (-(4 - κ) / 2 : ℝ) ≠ 0 ∧
    (∀ z ∈ annReg ρ R c, dynkinGen (tamedZField c) (-((Real.sqrt κ : ℝ) : ℂ)) (lyapV κ 0) z
      = (-(4 - κ) / 2) / ‖z‖ ^ 2) ∧
    (∀ z ∈ annReg ρ R c, (lyapV κ 0 z - lyapV κ 0 a) / (-(4 - κ) / 2)
      ≤ 2 * (lyapV κ 0 a + Real.log R + (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ)) / (4 - κ)) := by
  refine ⟨fun z hz => (contDiffAt_lyapV κ 0 hz).of_le three_le_smooth, by
    have : 0 < 4 - κ := by linarith
    intro h; linarith [div_eq_zero_iff.1 h], fun z hz => ?_, fun z hz => ?_⟩
  · have hz0 : 0 < z.im := hc.trans_le hz.2.2
    rw [dynkinGen_lyapV hκ hz.2.2 hz0]
    have hn2 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn2]
    have : z.re ^ 2 + z.im ^ 2 ≠ 0 := by positivity
    field_simp; ring
  · have hz0 : 0 < z.im := hc.trans_le hz.2.2
    have h4 : 0 < 4 - κ := by linarith
    have hge := lyapV_ge hκ hκ4.le 0 hz0
    have hlog : Real.log ‖z‖ ≤ Real.log R :=
      Real.log_le_log (hρ.trans_le hz.1) hz.2.1
    have e : (lyapV κ 0 z - lyapV κ 0 a) / (-(4 - κ) / 2)
        = 2 * (lyapV κ 0 a - lyapV κ 0 z) / (4 - κ) := by
      field_simp; ring
    rw [e]
    apply div_le_div_of_nonneg_right _ h4.le
    simp only [zero_mul, add_zero] at hge
    linarith

/-- Clock function data for `κ = 4`: `Φ = |log z|²`, `λ = 4`. -/
theorem clock_data_four {ρ R c : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (a : ℂ) :
    (∀ z : ℂ, 0 < z.im → ContDiffAt ℝ 3 logSq z) ∧ (4 : ℝ) ≠ 0 ∧
    (∀ z ∈ annReg ρ R c, dynkinGen (tamedZField c) (-((Real.sqrt 4 : ℝ) : ℂ)) logSq z
      = 4 / ‖z‖ ^ 2) ∧
    (∀ z ∈ annReg ρ R c, (logSq z - logSq a) / 4
      ≤ ((max |Real.log ρ| |Real.log R|) ^ 2 + Real.pi ^ 2) / 4) := by
  refine ⟨fun z hz => (contDiffAt_logSq hz).of_le three_le_smooth, by norm_num,
    fun z hz => dynkinGen_logSq_four hz.2.2 (hc.trans_le hz.2.2), fun z hz => ?_⟩
  have ha : 0 ≤ logSq a := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  have h1 := (le_abs_self (logSq z)).trans abs_logSq_le
  have h2 : Real.log ‖z‖ ^ 2 ≤ (max |Real.log ρ| |Real.log R|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (abs_log_norm_le_of_mem_annReg hρ hz) 2
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

theorem fwdClock_eq_of_stay {W : ℝ → ℝ} (hW : Continuous W) {a : ℂ} {ρ R c : ℝ} (hc : 0 < c)
    {T : ℝ} (hT : 0 ≤ T) (ha0 : 0 < a.im)
    (hin : ∀ s ∈ Icc (0 : ℝ) T, tamedZ W c a s ∈ annOpen ρ R c) :
    fwdClock W T a = ∫ s in (0 : ℝ)..T, 1 / ‖tamedZ W c a s‖ ^ 2 := by
  obtain ⟨-, heq⟩ := fwdMap_eq_tamedZ hW hc hT ha0 (fun s hs => (hin s hs).2.2.le)
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le hT] at hs
  simp only [heq s hs]

/-- **DF-3 (clock integrability, `κ < 4`).** On the event that the motion stays in the annular
region `{ρ < |z| < R, Im z > c}` up to time `T`, the expected clock is bounded uniformly in `ρ`
and `c`: `E[S_T(a); stay] ≤ 2(V(a) + log R + C_g)/(4−κ)`. -/
theorem lintegral_fwdClock_stay_le (hB : IsPreBrownianReal B P) (hBm : ∀ r, Measurable (B r))
    (hBc : ∀ ω, Continuous fun t => B t ω) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {a : ℂ} {ρ R c : ℝ} (T : ℝ≥0) (hρ : 0 < ρ) (hR : 0 < R) (hc : 0 < c)
    (ha : a ∈ annOpen ρ R c) :
    ∫⁻ ω, {ω | B 0 ω = 0 ∧ ∀ s ∈ Icc (0 : ℝ) T, tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c}.indicator
        (fun ω => ENNReal.ofReal (fwdClock (drive κ B ω) T a)) ω ∂P
      ≤ ENNReal.ofReal
        (2 * (lyapV κ 0 a + Real.log R + (4 - κ) / 4 * (2 * Real.pi ^ 2 / κ)) / (4 - κ)) := by
  obtain ⟨hΦ, hlam, hgen, hbound⟩ := clock_data_lt_four hκ hκ4 (R := R) hρ hc a
  have h := (prob_clock_le hB hBm hBc T hρ hR hc ha (lyapV κ 0) hΦ hlam hgen hbound
    (u := 1) one_pos).1
  refine le_of_eq_of_le (lintegral_congr fun ω => ?_) h
  by_cases hω : ω ∈ {ω | B 0 ω = 0 ∧ ∀ s ∈ Icc (0 : ℝ) T,
      tamedZ (drive κ B ω) c a s ∈ annOpen ρ R c}
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω,
      fwdClock_eq_of_stay (continuous_drive_ns hBc κ ω) hc T.coe_nonneg (hc.trans ha.2.2) hω.2]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]

end NonSwallow
end QuantumZipper
